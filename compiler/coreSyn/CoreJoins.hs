{-# LANGUAGE CPP #-}

module CoreJoins (
  findJoinsInPgm, findJoinsInExpr, eraseJoins,
) where

import CoreSyn
import Id
import IdInfo
import Maybes
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
findJoinsInPgm pgm = map (\bind -> propagateBinderSorts $ initFJ (fjTopBind bind)) pgm

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
         <- mfix $ \ ~(_, _, join_arities) ->
                     fjLet join_arities bind body
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
       is_candidate <- isCandidateFJ v
       let anal = if is_candidate then oneGoodId v (length args) else emptyJoinAnal
           full_anal = combineManyJoinAnals (anal : map markAllVarsBad arg_anals)
       return (mkApps (Var v) args', full_anal)

fjLet :: Maybe [JoinArity] -> CoreBind -> CoreExpr
      -> FJM (CoreExpr, JoinAnal, Maybe [JoinArity])
fjLet rec_join_arities bind body
  = do (bind', bind_anal, body', body_anal)
         <- do (bind', bind_anal, bndrs)
                 <- vars_bind rec_join_arities bind
               -- Do the body
               withCandidatesFJ bndrs $ do
                 (body', body_anal) <- fjExpr body

                 return (bind', bind_anal, body', body_anal)
       let new_let = Let bind' body'

           will_be_joins = isJust rec_join_arities

           real_bind_anal | will_be_joins         = bind_anal
                          | otherwise             = markAllVarsBad bind_anal
                              -- Everything escapes which is free in the bindings

           real_bind_anal_wo_binders
             | is_rec    = real_bind_anal `removeAllFromJoinAnal` binders
             | otherwise = real_bind_anal

           let_anal = (body_anal `removeAllFromJoinAnal` binders)
                        `combineJoinAnals` real_bind_anal_wo_binders

           all_anal | is_rec    = bind_anal `combineJoinAnals` body_anal    -- Still includes binders of
                    | otherwise = body_anal                                 -- this let(rec)

           join_arities = decideSort bind all_anal

       return (
           new_let,
           let_anal,
           join_arities
         )
  where
    binders        = bindersOf bind
    is_rec         = case bind of NonRec {} -> False; _ -> True

    vars_bind :: Maybe [JoinArity]
              -> CoreBind
              -> FJM (CoreBind,
                      JoinAnal,            -- good vars; bad vars
                      [Id])   -- extension to environment

    vars_bind rec_join_arities (NonRec binder rhs) = do
        (rhs', bind_anal) <- fjRhs rhs
        (bndr', bndr_anal) <- fjBndr binder
        let bndr'' = case rec_join_arities of
                       Just [arity] -> asJoinId binder arity
                       Just _       -> panic "vars_bind"
                       Nothing | isId bndr' -> zapJoinId bndr'
                               | otherwise  -> bndr'

        return (NonRec bndr'' rhs',
                bind_anal `combineJoinAnals` bndr_anal, [binder])


    vars_bind rec_join_arities (Rec pairs)
      = let
          (binders, rhss) = unzip pairs
        in
        withCandidatesFJ binders $ do
          (bndrs', bndr_anals) <- mapAndUnzipM fjBndr binders
          (rhss', rhs_anals)
            <- mapAndUnzipM fjRhs rhss
          let
            anal = combineManyJoinAnals (bndr_anals ++ rhs_anals)
            bndrs'' = case rec_join_arities of
                        Just arities -> zipWith asJoinId bndrs' arities
                        Nothing      -> map zapJoinId bndrs'

          return (Rec (bndrs'' `zip` rhss'),
                  anal, binders)

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

newtype FJM a = FJM
    { unFJM :: CandSet
            -> a
    }

type CandSet    = IdSet

initFJ :: FJM a -> a
initFJ m = unFJM m emptyVarSet

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

withCandidatesFJ :: [Id] -> FJM a -> FJM a
withCandidatesFJ ids expr
   =    FJM $   \env
   -> unFJM expr (extendVarSetList env ids)

withoutCandidatesFJ :: [Id] -> FJM a -> FJM a
withoutCandidatesFJ ids expr
   =    FJM $   \env
   -> unFJM expr (delVarSetList env ids)

isCandidateFJ :: Id -> FJM Bool
isCandidateFJ v = FJM $ \env -> v `elemVarSet` env

-- ---------------------------------------------------------------------------
-- Join Analyses
-- ---------------------------------------------------------------------------

type JoinAnal = (GoodSet, BadSet)
type GoodSet = IdEnv (Id, JoinArity)
type BadSet = IdSet

emptyJoinAnal :: JoinAnal
emptyJoinAnal = (emptyVarEnv, emptyVarSet)

isEmptyJoinAnal :: JoinAnal -> Bool
isEmptyJoinAnal (good, bad) = isEmptyVarEnv good && isEmptyVarSet bad

oneGoodId :: Id -> JoinArity -> JoinAnal
oneGoodId id arity = (unitVarEnv id (id, arity), emptyVarSet)

toBadSet :: GoodSet -> BadSet
toBadSet = mapVarEnv fst

combineJoinAnals :: JoinAnal -> JoinAnal -> JoinAnal
combineJoinAnals (good1, bad1) (good2, bad2)
  | isEmptyVarEnv good2
  = (good1', bad')
  | isEmptyVarEnv good1
  = (good2', bad')
  | otherwise
  = (good', bad' `unionVarSet` newly_bad)
  where
    good1' = good1 `minusVarEnv` bad2
    good2' = good2 `minusVarEnv` bad1
    bad'   = bad1  `unionVarSet` bad2

    -- TODO Avoid extra traversal if possible. What we *really* want is
    -- a function of type
    --   (a -> a -> Either a b) -> VarEnv a -> VarEnv a -> (VarEnv a, VarEnv b),
    -- but that seems a bit narrow to add to VarEnv (and UniqFM).
    good' = plusMaybeVarEnv_C good_if_equal good1' good2'
    newly_bad = mapMaybeVarEnv id $ intersectVarEnv_C bad_if_unequal good1' good2'

    good_if_equal pair1@(var, arity1) (_var, arity2)
      = ASSERT(var == _var)
        if arity1 == arity2 then Just pair1 else Nothing
    bad_if_unequal (var, arity1) (_var, arity2)
      = ASSERT(var == _var)
        if arity1 == arity2 then Nothing else Just var -- bad set only has var

combineManyJoinAnals :: [JoinAnal] -> JoinAnal
combineManyJoinAnals []     = emptyJoinAnal
combineManyJoinAnals (a:as) = foldr combineJoinAnals a as

markAllVarsBad :: JoinAnal -> JoinAnal
markAllVarsBad (good, bad) = (emptyVarEnv, toBadSet good `unionVarSet` bad)

removeAllFromJoinAnal :: JoinAnal -> [Id] -> JoinAnal
removeAllFromJoinAnal (good, bad) ids
  = (good `delVarEnvList` ids, bad `delVarSetList` ids)

findGoodId :: JoinAnal -> Id -> Maybe JoinArity
findGoodId (good, _bad) id = snd <$> lookupVarEnv good id

-- ---------------------------------------------------------------------------
-- Rewriting Occurrences
-- ---------------------------------------------------------------------------

propagateBinderSorts :: CoreBind -> CoreBind
-- Change occurrences so that occurrences of join vars appear to be join vars
-- and similarly for value vars
propagateBinderSorts bind
  = let (_ins', bind') = rw_bind emptyInScopeSet bind in bind'
  where
    rw_bind ins (NonRec bndr rhs)
      = (extendInScopeSet ins bndr, NonRec bndr (rw_expr ins rhs))
    rw_bind ins (Rec pairs)
      = (ins', Rec [(bndr, rw_expr ins' rhs) | (bndr, rhs) <- pairs])
      where
        ins' = extendInScopeSetList ins (map fst pairs)

    rw_expr ins (Var var)
      = Var var'
      where
        bndr = lookupInScope ins var `orElse` var
        var' | Just arity <- isJoinId_maybe bndr
             = asJoinId var arity
             | isJoinId var, not (isJoinId bndr)
             = WARN(True, text "Join variable was no longer valid:" <+> ppr var)
               zapJoinId var
             | otherwise
             = var
    rw_expr ins (App fun arg)
      = App (rw_expr ins fun) (rw_expr ins arg)
    rw_expr ins (Lam bndr body)
      = Lam bndr (rw_expr (extendInScopeSet ins bndr) body)
    rw_expr ins (Let bind body)
      = Let bind' (rw_expr ins' body)
      where
        (ins', bind') = rw_bind ins bind
    rw_expr ins (Case scrut bndr ty alts)
      = Case (rw_expr ins scrut) bndr ty (map (rw_alt ins) alts)
    rw_expr ins (Cast expr co)
      = Cast (rw_expr ins expr) co
    rw_expr ins (Tick ti expr)
      = Tick ti (rw_expr ins expr)
    rw_expr _   other
      = other

    rw_alt ins (con, bndrs, rhs)
      = (con, bndrs, rw_expr (extendInScopeSetList ins bndrs) rhs)

-- ---------------------------------------------------------------------------
-- Misc.
-- ---------------------------------------------------------------------------

lambdaCount :: Expr a -> JoinArity
-- ^ lambdaCount sees how many leading lambdas there are,
--   *not* skipping casts and *counting* type lambdas. We just need to knew
--   whether a given application is total (*including* all type arguments)
lambdaCount expr = length bndrs where (bndrs, _) = collectBinders expr

decideSort :: CoreBind -> JoinAnal -> Maybe [JoinArity]
-- ^ Checks whether each binding is elegible to be a join point, given the
--   analysis. Besides needing to be in the analysis's good set, a join point
--   cannot be polymorphic in its return type, since its context is fixed and
--   thus its type cannot vary.
decideSort bind anal
  = sequence (map decide (flattenBinds [bind]))
  where
    decide (bndr, rhs)
      | Just arity <- findGoodId anal bndr
      , arity == lambdaCount rhs -- TODO loosen restriction (carefully!)
      , good_type arity emptyVarSet (idType bndr)
      = Just arity
      | otherwise
      = Nothing
      where
        good_type 0 tvs ty
          = isEmptyVarSet (tvs `intersectVarSet` tyCoVarsOfType ty)
        good_type n tvs ty
          | Just (t, ty') <- splitForAllTy_maybe ty
          = good_type (n-1) (extendVarSet tvs t) ty'
          | otherwise
          = good_type (n-1) tvs (funResultTy ty)
