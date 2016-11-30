{-# LANGUAGE TupleSections, ViewPatterns #-}

module CoreCxts (
  CxtId,
  ExprWithCxts, BindWithCxts, AltWithCxts,
  CoreExprWithCxts, CoreBindWithCxts, CoreAltWithCxts,
  AnnExprWithCxts, AnnBindWithCxts, AnnAltWithCxts,

  addContextsToPgm, addContextsToTopBind,
  markCxt, markAnnCxt, markCoreCxt, markCoreAnnCxt,
  removeCxts, removeCxtsFromBind,

  CxtSplit(..), splitCxt, ignoreCxt, splitAnnCxt, ignoreAnnCxt,
) where

import Coercion
import CoreArity
import CoreSyn
import CoreUtils
import FastString
import Id
import PrelNames  ( cxtMarkerKey, cxtMarkerName )
import Type
import UniqSupply

type CxtId = Var

type ExprWithCxts b = Expr b
type BindWithCxts b = Bind b
type AltWithCxts  b = Alt  b

type CoreExprWithCxts = CoreExpr
type CoreBindWithCxts = CoreBind
type CoreAltWithCxts  = CoreAlt

type AnnExprWithCxts b a = AnnExpr b a
type AnnBindWithCxts b a = AnnBind b a
type AnnAltWithCxts  b a = AnnAlt  b a

addContextsToPgm :: CoreProgram -> UniqSM [CoreBindWithCxts]
addContextsToPgm = mapM addContextsToTopBind

addContextsToTopBind :: CoreBind -> UniqSM CoreBindWithCxts
addContextsToTopBind = addCxtsBind

-------------------

data CxtSplit bndr a = InNewCxt  bndr a
                     | InSameCxt a

splitCxt :: ExprWithCxts b -> CxtSplit b (ExprWithCxts b)
splitCxt (Let (NonRec bndr rhs) body)
  | isCxtMarker rhs = InNewCxt bndr body
splitCxt other      = InSameCxt other

ignoreCxt :: ExprWithCxts b -> ExprWithCxts b
ignoreCxt (splitCxt -> InNewCxt _ body) = body
ignoreCxt other                         = other

splitAnnCxt :: AnnExprWithCxts b a -> CxtSplit b (AnnExprWithCxts b a)
splitAnnCxt (_, AnnLet (AnnNonRec bndr rhs) body)
  | isAnnCxtMarker rhs = InNewCxt bndr body
splitAnnCxt other      = InSameCxt other

ignoreAnnCxt :: AnnExprWithCxts b a -> AnnExprWithCxts b a
ignoreAnnCxt (splitAnnCxt -> InNewCxt _ body) = body
ignoreAnnCxt other                            = other

markCxt :: b -> Type -> ExprWithCxts b -> ExprWithCxts b
markCxt cid ty expr = Let (NonRec cid marker) expr
  where
    marker = mkCxtMarker ty

markCoreCxt :: CxtId -> CoreExprWithCxts -> CoreExprWithCxts
markCoreCxt cid = markCxt cid (idType cid)

mkCxtMarker :: Type -> ExprWithCxts b
mkCxtMarker = varToCoreExpr . mkCxtMarkerId

isCxtMarker :: ExprWithCxts b -> Bool
isCxtMarker (Var v)             = isCxtMarkerId v
isCxtMarker (Coercion co)
  | Just v <- getCoVar_maybe co = isCxtMarkerId v
isCxtMarker _                   = False

markAnnCxt :: a -> b -> Type -> AnnExprWithCxts b a -> AnnExpr' b a
markAnnCxt ann cid ty expr = AnnLet (AnnNonRec cid (ann, marker)) expr
  where
    marker = mkAnnCxtMarker ty

markCoreAnnCxt :: a -> CxtId -> AnnExprWithCxts CoreBndr a
               -> AnnExpr' CoreBndr a
markCoreAnnCxt ann cid = markAnnCxt ann cid (idType cid)

mkAnnCxtMarker :: Type -> AnnExpr' b a
mkAnnCxtMarker = to_ann_expr . mkCxtMarkerId
  where
    to_ann_expr v | isCoVar v = AnnCoercion (mkCoVarCo v)
                  | otherwise = AnnVar v

isAnnCxtMarker :: AnnExprWithCxts b a -> Bool
isAnnCxtMarker (_, AnnVar v)    = isCxtMarkerId v
isAnnCxtMarker (_, AnnCoercion co)
  | Just v <- getCoVar_maybe co = isCxtMarkerId v
isAnnCxtMarker _                = False

removeCxts :: ExprWithCxts b -> Expr b
removeCxts (splitCxt -> InNewCxt _ expr)
                           = removeCxts expr
removeCxts (App fun arg)   = App (removeCxts fun) (removeCxts arg)
removeCxts (Lam bndr body) = Lam bndr (removeCxts body)
removeCxts (Let bind body) = Let (removeCxtsFromBind bind) (removeCxts body)
removeCxts (Case e b t as) = Case (removeCxts e) b t
                                  [ (con, bndrs, removeCxts rhs)
                                  | (con, bndrs, rhs) <- as ]
removeCxts (Cast expr co)  = Cast (removeCxts expr) co
removeCxts (Tick ti expr)  = Tick ti (removeCxts expr)
removeCxts other           = other

removeCxtsFromBind :: BindWithCxts b -> Bind b
removeCxtsFromBind (NonRec bndr rhs) = NonRec bndr (removeCxts rhs)
removeCxtsFromBind (Rec pairs) = Rec [ (bndr, removeCxts rhs)
                                     | (bndr, rhs) <- pairs ]

--------------------

mkCxtMarkerId :: Type -> Id
mkCxtMarkerId ty = globaliseId $ mkLocalIdOrCoVar cxtMarkerName ty
  -- Make it global so that CoreSubst doesn't freak out

isCxtMarkerId :: Id -> Bool
isCxtMarkerId id = idUnique id == cxtMarkerKey

addCxtsBind :: CoreBind -> UniqSM CoreBindWithCxts
addCxtsBind bind
  = case bind of
      NonRec bndr rhs -> do (bndr', rhs') <- do_pair (bndr, rhs)
                            return $ NonRec bndr' rhs'
      Rec pairs       -> Rec <$> mapM do_pair pairs
  where
    do_pair (bndr, rhs)
      | isId bndr
      , Just join_arity <- isJoinId_maybe bndr
      , let (bndrs, body) = splitJoinPoint join_arity rhs
      = do body' <- addCxtsTail body
           return (bndr, mkLams bndrs body')
      | otherwise
      = (bndr,) <$> addCxtsNonTail (fsLit "rhs") rhs

addCxtsNonTail :: FastString -> CoreExpr -> UniqSM CoreExprWithCxts
-- ^ Add context info to an expression in non-tail position. There will be a
-- fresh CxtId created; the FastString argument is used to name it (for more
-- informative traces).
addCxtsNonTail _    (Type ty)
  = return (Type ty)
addCxtsNonTail _    (Coercion co)
  = return (Coercion co)
addCxtsNonTail _    (Var v)
  | isJoinId v
  = return (Var v)
addCxtsNonTail name expr
  = do cid   <- mkSysLocalOrCoVarM name (exprType expr)
       expr' <- addCxtsExpr expr
       return (markCoreCxt cid expr')

addCxtsTail :: CoreExpr -> UniqSM CoreExprWithCxts
addCxtsTail
  = addCxtsExpr

addCxtsExpr :: CoreExpr -> UniqSM CoreExprWithCxts
addCxtsExpr expr
  = case expr of
      Var id           -> return $ Var id
      Lit lit          -> return $ Lit lit
      App {}           -> do let (fun, args) = collectArgs expr
                             foldl App <$> addCxtsNonTail (fsLit "app") fun
                                       <*> mapM (addCxtsNonTail (fsLit "arg"))
                                                 args
      Lam {}           -> do let (bndrs, body) = collectBinders expr
                             foldr Lam <$> addCxtsNonTail (fsLit "lam") body
                                       <*> pure bndrs
      Let bind body    -> Let <$> addCxtsBind bind <*> addCxtsTail body
      Case e b ty alts -> Case <$> addCxtsNonTail (fsLit "case") e
                               <*> pure b
                               <*> pure ty
                               <*> mapM addCxtsAlt alts
      Cast e co        -> Cast <$> addCxtsNonTail (fsLit "cast") e
                               <*> pure co
      Tick ti e        -> Tick ti <$> addCxtsNonTail (fsLit "tick") e
      Type ty          -> return $ Type ty
      Coercion co      -> return $ Coercion co

addCxtsAlt :: CoreAlt -> UniqSM CoreAltWithCxts
addCxtsAlt (con, bndrs, rhs) = (con, bndrs,) <$> addCxtsTail rhs
