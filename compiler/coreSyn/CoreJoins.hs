{-# LANGUAGE CPP #-}

module CoreJoins (
  findJoinsInPgm, findJoinsInExpr, eraseJoins,
) where

import CoreSyn
import CoreUtils
import Id
import MonadUtils
import Outputable
import PprCore ()
import Rules
import Type
import Util
import VarEnv
import VarSet

import Control.Monad

#include "HsVersions.h"

findJoinsInPgm :: CoreProgram -> CoreProgram
findJoinsInPgm pgm = propagateBinders $ map (\bind -> initFJ $ fjTopBind bind) pgm

findJoinsInExpr :: CoreExpr -> CoreExpr
findJoinsInExpr expr = initFJ $ do (expr', anal) <- fjExpr expr
                                   MASSERT(isEmptyJoinAnal anal)
                                   return expr'

eraseJoins :: CoreProgram -> CoreProgram
-- ^ Remove all join points from a program, turning them into ordinary let
-- bindings. This is generally only useful for testing how useful join points
-- are.
eraseJoins = map doBind
  where
    doBind (NonRec bndr rhs) = NonRec (zapBndrSort bndr) (doExpr rhs)
    doBind (Rec pairs) = Rec [ (zapBndrSort bndr, doExpr rhs)
                             | (bndr, rhs) <- pairs ]

    doExpr (App fun arg)   = App (doExpr fun) (doExpr arg)
    doExpr (Lam bndr body) = Lam (zapBndrSort bndr) (doExpr body)
    doExpr (Let bind body) = Let (doBind bind) (doExpr body)
    doExpr (Case scrut bndr ty alts)
      = Case (doExpr scrut) (zapBndrSort bndr) ty
             [ (con, map zapBndrSort bndrs, doExpr rhs)
             | (con, bndrs, rhs) <- alts ]
    doExpr (Cast expr co)  = Cast (doExpr expr) co
    doExpr (Tick ti expr)  = Tick ti (doExpr expr)
    doExpr other = other

data BndrSort = JoinBndr | ValBndr deriving (Eq)

setBndrSort :: Var -> BndrSort -> Int -> Var
setBndrSort b sort ar | not (isId b) = b
                      | sort == JoinBndr = asJoinId b ar
                      | otherwise        = zapJoinId b

zapBndrSort :: Var -> Var
zapBndrSort b | isId b    = zapJoinId b
              | otherwise = b

-------------------------
-- Finding join points --
-------------------------

fjTopBind :: CoreBind -> FJM CoreBind
fjTopBind (NonRec bndr expr)
  = do (bndr', expr') <- fjTopPair (bndr, expr)
       return $ NonRec bndr' expr'
fjTopBind (Rec pairs)
  = Rec <$> (mapM fjTopPair pairs)

fjTopPair :: (CoreBndr, CoreExpr) -> FJM (CoreBndr, CoreExpr)
fjTopPair (bndr, expr)
  = do (expr', _) <- fjExpr expr
       return (zapBndrSort bndr, expr') -- can't have top-level join

fjExpr :: CoreExpr -> FJM (CoreExpr, JoinAnal)
fjExpr (Lit l)       = return (Lit l, emptyJoinAnal)
fjExpr (Coercion co) = return (Coercion co, emptyJoinAnal)
fjExpr (Type ty)     = return (Type ty, emptyJoinAnal)

fjExpr (Var v)
  = fjApp v []
fjExpr expr@(App {})
  | Var v <- fun
  = fjApp v args
  | otherwise
  = do (fun', fun_anal)   <- fjExpr fun
       (args', arg_anals) <- mapAndUnzipM fjExpr args
       return (mkApps fun' args',
                markAllVarsBad $ combineManyJoinAnals (fun_anal : arg_anals))
  where
    (fun, args) = collectArgs expr
fjExpr expr@(Lam {})
  = do let (bndrs, body) = collectBinders expr
       (body', anal) <- withoutCandidatesFJ bndrs $ fjExpr body
       return (mkLams [ zapBndrSort bndr | bndr <- bndrs ] body', markAllVarsBad anal)
fjExpr (Let bind body)
  = do (expr', anal, _)
         <- mfix $ \ ~(_, _, sort) ->
                     fjLet sort bind body
       return (expr', anal)
fjExpr (Case scrut bndr ty alts)
  = do (scrut', scrut_anal) <- fjExpr scrut
       (alts', alt_anals) <- withoutCandidatesFJ [bndr] $ mapAndUnzipM fjAlt alts
       let anal = combineManyJoinAnals (markAllVarsBad scrut_anal : alt_anals)
       return (Case scrut' (zapBndrSort bndr) ty alts', anal)
fjExpr (Cast expr co)
  = do (expr', anal) <- fjExpr expr
       return (Cast expr' co, markAllVarsBad anal)
fjExpr (Tick ti expr)
  = do (expr', anal) <- fjExpr expr
       return (Tick ti expr', markAllVarsBad anal)

fjApp :: Id -> [CoreArg] -> FJM (CoreExpr, JoinAnal)
fjApp v args
  = do (args', arg_anals) <- mapAndUnzipM fjExpr args
       m_total_arity <- lookupCandidateFJ v
       let anal = this_anal (length args) m_total_arity
           full_anal = combineManyJoinAnals (anal : map markAllVarsBad arg_anals)
       return (mkApps (Var v) args', full_anal)
  where
    this_anal _ Nothing = emptyJoinAnal
    this_anal n_args (Just total_arity)
      | n_args == total_arity = oneGoodId v
      | otherwise             = oneBadId v

fjLet :: BndrSort -> CoreBind -> CoreExpr -> FJM (CoreExpr, JoinAnal, BndrSort)
fjLet rec_sort bind body
  = do (bind', bind_anal, body', body_anal)
         <- do (bind', bind_anal, env_ext)
                 <- vars_bind rec_sort bind
               -- Do the body
               withCandidatesFJ env_ext $ do
                 (body', body_anal) <- fjExpr body

                 return (bind', bind_anal, body', body_anal)
       let new_let = Let bind' body'

           real_bind_anal | rec_sort == JoinBndr  = bind_anal
                          | otherwise             = markAllVarsBad bind_anal
                              -- Everything escapes which is free in the bindings

           real_bind_anal_wo_binders
             | is_rec    = real_bind_anal `removeAllFromJoinAnal` binders
             | otherwise = real_bind_anal

           let_anal = (body_anal `removeAllFromJoinAnal` binders)
                        `combineJoinAnals` real_bind_anal_wo_binders

           all_anal | is_rec    = bind_anal `combineJoinAnals` body_anal    -- Still includes binders of
                    | otherwise = body_anal                                 -- this let(rec)

           sort | couldBeJoinBind bind
                , binders `allInGoodSet` all_anal
                = JoinBndr
                | otherwise
                = ValBndr

       return (
           new_let,
           let_anal,
           sort
         )
  where
    binders        = bindersOf bind
    is_rec         = case bind of NonRec {} -> False; _ -> True

    vars_bind :: BndrSort                  -- Join points or values?
              -> CoreBind
              -> FJM (CoreBind,
                      JoinAnal,            -- free vars; good vars
                      [(Id, TotalArity)])  -- extension to environment

    vars_bind sort (NonRec binder rhs) = do
        (rhs', bind_anal) <- fjRhs rhs
        (bndr', bndr_anal) <- fjBndr binder
        let
            join_arity = lambdaCount rhs

        return (NonRec (setBndrSort bndr' sort join_arity) rhs',
                bind_anal `combineJoinAnals` bndr_anal, [(bndr', join_arity)])


    vars_bind sort (Rec pairs)
      = let
          (binders, rhss) = unzip pairs
          env_ext = [ (b, lambdaCount rhs)
                    | (b,rhs) <- pairs ]
        in
        withCandidatesFJ env_ext $ do
          (bndrs', bndr_anals) <- mapAndUnzipM fjBndr binders
          (rhss', rhs_anals)
            <- mapAndUnzipM fjRhs rhss
          let
            anal = combineManyJoinAnals (bndr_anals ++ rhs_anals)
            bndrs'' = [ setBndrSort bndr' sort ar
                      | (bndr', (_, ar)) <- bndrs' `zip` env_ext ]

          return (Rec (bndrs'' `zip` rhss'),
                  anal, env_ext)

fjRhs :: CoreExpr -> FJM (CoreExpr, JoinAnal)
fjRhs expr = do let (bndrs, body) = collectBinders expr
                (body', anal) <- withoutCandidatesFJ bndrs $ fjExpr body
                return (mkLams [ zapBndrSort bndr | bndr <- bndrs ] body', anal)

fjAlt :: CoreAlt -> FJM (CoreAlt, JoinAnal)
fjAlt (con, bndrs, rhs)
  = do (rhs', anal) <- withoutCandidatesFJ bndrs $ fjExpr rhs
       return ((con, [ zapBndrSort bndr | bndr <- bndrs ], rhs'), anal)

fjBndr :: CoreBndr -> FJM (CoreBndr, JoinAnal)
fjBndr bndr
  | not (isId bndr)
  = return (bndr, emptyJoinAnal)
  | otherwise
  = do (rules', anals) <- mapAndUnzipM fjRule (idCoreRules bndr)
       (unf', unf_anal) <- fjUnfolding (realIdUnfolding bndr)
       let bndr' = bndr `setIdSpecialisation` (mkRuleInfo rules')
                        `setIdUnfolding` unf'
           anal  = combineManyJoinAnals (unf_anal : anals)
       return (bndr', anal)

-- FIXME Right now we just brazenly go in and tweak the expressions stored in
-- rules and unfoldings. Surely we should be more careful than that. - LVWM 

fjRule :: CoreRule -> FJM (CoreRule, JoinAnal)
fjRule rule@(BuiltinRule {})
  = return (rule, emptyJoinAnal)
fjRule rule@(Rule { ru_bndrs = bndrs, ru_rhs = rhs })
  = do (rhs', anal) <- withoutCandidatesFJ bndrs $ fjRhs rhs
         -- See Note [Rules]
       return (rule { ru_rhs = rhs' }, anal)

fjUnfolding :: Unfolding -> FJM (Unfolding, JoinAnal)
fjUnfolding unf@(CoreUnfolding { uf_src = src, uf_tmpl = rhs })
  | isStableSource src
  = do (rhs', anal) <- fjRhs rhs
       return (unf { uf_tmpl = rhs' }, anal)
  | otherwise
  = return (unf, emptyJoinAnal)
      -- Should be the same as the RHS, and we don't want exponential behavior
      -- (see CoreFVs.idUnfoldingVars). Downside: We don't find joins inside.
fjUnfolding unf@(DFunUnfolding { df_bndrs = bndrs, df_args = args })
  = do (args', anals) <- withoutCandidatesFJ bndrs $ mapAndUnzipM fjExpr args
       return (unf { df_args = args' }, combineManyJoinAnals anals)
fjUnfolding unf
  = return (unf, emptyJoinAnal)

{-
Note [Rules]
~~~~~~~~~~~~

Right now, we do the obvious thing with rules, which is to treat each rule RHS
as an alternate RHS for the binder. This is wrong, but should (!) only be wrong
in the safe direction.

The difficulty is with arity. Suppose we have:

  let j :: Int -> Int
      j y = 2 * y
      k :: Int -> Int -> Int
      {-# RULES "SPEC k 0" k 0 = j #-}
      k x y = x + 2 * y
  in ...

(By "arity" here we mean arity counting type args, as usual with join points.)
Now suppose that both j and k appear only as saturated tail calls in the body.
Thus we would like to make them both join points. The rule complicates matters,
though, as its RHS has an unapplied occurrence of j. *However*, any application
of k will be saturated (since k is a join point), so if the rule fires, it still
results in a valid tail call:

  k 0 q ==> j q

Detecting this situation seems difficult, however, so for the moment we sadly
forbid j as a join point. 

-}

-- ---------------------------------------------------------------------------
-- Monad
-- ---------------------------------------------------------------------------

-- There's a lot of stuff to pass around, so we use this FJM monad to
-- help.  All the stuff here is only passed *down*.

newtype FJM a = FJM
    { unFJM :: CandSet
            -> a
    }

type TotalArity = Int -- Counting types AND values
type CandSet    = IdEnv TotalArity

initFJ :: FJM a -> a
initFJ m = unFJM m emptyVarEnv

{-# INLINE thenFJ #-}
{-# INLINE returnFJ #-}

returnFJ :: a -> FJM a
returnFJ e = FJM $ \_ -> e

thenFJ :: FJM a -> (a -> FJM b) -> FJM b
thenFJ m k = FJM $ \env
  -> unFJM (k (unFJM m env)) env

instance Functor FJM where
    fmap = liftM

instance Applicative FJM where
    pure = returnFJ
    (<*>) = ap

instance Monad FJM where
    (>>=)  = thenFJ

instance MonadFix FJM where
    mfix expr = FJM $ \env ->
                      let result = unFJM (expr result) env
                      in  result

-- Functions specific to this monad:

withCandidatesFJ :: [(Id, Int)] -> FJM a -> FJM a
withCandidatesFJ ids_w_arity expr
   =    FJM $   \env
   -> unFJM expr (extendVarEnvList env ids_w_arity)

withoutCandidatesFJ :: [Id] -> FJM a -> FJM a
withoutCandidatesFJ ids expr
   =    FJM $   \env
   -> unFJM expr (delVarEnvList env ids)

lookupCandidateFJ :: Id -> FJM (Maybe TotalArity)
lookupCandidateFJ v = FJM $ \env -> lookupVarEnv env v

-- ---------------------------------------------------------------------------
-- Join Analyses
-- ---------------------------------------------------------------------------

type JoinAnal = (GoodSet, BadSet)
type GoodSet = IdSet
type BadSet = IdSet

emptyJoinAnal :: JoinAnal
emptyJoinAnal = (emptyVarSet, emptyVarSet)

isEmptyJoinAnal :: JoinAnal -> Bool
isEmptyJoinAnal (good, bad) = isEmptyVarSet good && isEmptyVarSet bad

oneGoodId :: Id -> JoinAnal
oneGoodId id = (unitVarSet id, emptyVarSet)

oneBadId :: Id -> JoinAnal
oneBadId id = (emptyVarSet, unitVarSet id)

combineJoinAnals :: JoinAnal -> JoinAnal -> JoinAnal
combineJoinAnals (good1, bad1) (good2, bad2)
  = (good, bad)
  where
    good = (good1 `minusVarSet` bad2) `unionVarSet`
           (good2 `minusVarSet` bad1)
    bad  = bad1 `unionVarSet` bad2

combineManyJoinAnals :: [JoinAnal] -> JoinAnal
combineManyJoinAnals []     = emptyJoinAnal
combineManyJoinAnals (a:as) = foldr combineJoinAnals a as

markAllVarsBad :: JoinAnal -> JoinAnal
markAllVarsBad (good, bad) = (emptyVarSet, good `unionVarSet` bad)

removeFromJoinAnal :: JoinAnal -> Id -> JoinAnal
removeFromJoinAnal (good, bad) id
  = (good `delVarSet` id, bad `delVarSet` id)

removeAllFromJoinAnal :: JoinAnal -> [Id] -> JoinAnal
removeAllFromJoinAnal (good, bad) ids
  = (good `delVarSetList` ids, bad `delVarSetList` ids)

inGoodSet :: Id -> JoinAnal -> Bool
inGoodSet id (good, _bad) = id `elemVarSet` good

allInGoodSet :: [Id] -> JoinAnal -> Bool
allInGoodSet ids (good, _bad) = isEmptyVarSet (mkVarSet ids `minusVarSet` good)

-- ---------------------------------------------------------------------------
-- Misc.
-- ---------------------------------------------------------------------------

lambdaCount :: Expr a -> TotalArity
-- ^ lambdaCount sees how many leading lambdas there are,
--   *not* skipping casts and *counting* type lambdas. We just need to knew
--   whether a given application is total (*including* all type arguments)
lambdaCount expr = length bndrs where (bndrs, _) = collectBinders expr

couldBeJoinBind :: CoreBind -> Bool
-- ^ Checks whether each binding is elegible to be a join point. A join point
--   cannot be polymorphic in its return type, since its context is fixed and
--   thus its type cannot vary.
couldBeJoinBind bind
  = case bind of NonRec bndr rhs -> good (bndr, rhs)
                 Rec pairs       -> all good pairs
  where
    good (bndr, rhs) = go emptyVarSet (idType bndr) rhs
      where
        go tvs ty (Lam _ body)
          | Just (t, ty') <- splitForAllTy_maybe ty
          = go (extendVarSet tvs t) ty' body
          | otherwise
          = go tvs (funResultTy ty) body
        go tvs ty _
          = isEmptyVarSet (tvs `intersectVarSet` tyCoVarsOfType ty)
