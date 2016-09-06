{-# LANGUAGE TupleSections, ViewPatterns #-}

module CoreCxts (
  CxtId,
  ExprWithCxts, BindWithCxts, AltWithCxts,
  CoreExprWithCxts, CoreBindWithCxts, CoreAltWithCxts,

  addContextsToPgm, addContextsToTopBind,
  isCxtMarkerId, isCxtMarker, isCxtMarker_maybe, mkCxtMarkerId,
  markCxt, markCxtAnn, markCxtTagged, markCxtTaggedAnn,
  removeCxts, removeCxtsFromBind,

  CxtSplit(..), splitCxt, ignoreCxt,
) where

import CoreSyn
import CoreUtils
import FastString
import Id
import Outputable
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

addContextsToPgm :: CoreProgram -> UniqSM [CoreBindWithCxts]
addContextsToPgm = mapM addContextsToTopBind

addContextsToTopBind :: CoreBind -> UniqSM CoreBindWithCxts
addContextsToTopBind = addCxtsBind

mkCxtMarkerId :: Type -> Id
mkCxtMarkerId ty = mkLocalIdOrCoVar cxtMarkerName ty

isCxtMarkerId :: Id -> Bool
isCxtMarkerId id = idUnique id == cxtMarkerKey

isCxtMarker :: CoreBindWithCxts -> Bool
isCxtMarker (NonRec bndr _) = isCxtMarkerId bndr
isCxtMarker _               = False

isCxtMarker_maybe :: CoreBindWithCxts -> Maybe CxtId
isCxtMarker_maybe (NonRec bndr rhs)
  | isCxtMarkerId bndr
  = case rhs of Var cid -> Just cid
                other   -> pprPanic "isCxtMarker_maybe" (ppr other)
isCxtMarker_maybe _
  = Nothing

data CxtSplit a = InNewCxt  CxtId a
                | InSameCxt a

splitCxt :: CoreExprWithCxts -> CxtSplit CoreExprWithCxts
splitCxt (Let bind body)
  | Just cid <- isCxtMarker_maybe bind = InNewCxt cid body
splitCxt other                         = InSameCxt other

ignoreCxt :: CoreExprWithCxts -> CoreExprWithCxts
ignoreCxt (splitCxt -> InNewCxt _ body) = body
ignoreCxt other                         = other

markCxt :: CxtId -> CoreExprWithCxts -> CoreExprWithCxts
markCxt cid expr = Let (NonRec marker (Var cid)) expr
  where
    marker = mkCxtMarkerId (idType cid)

markCxtAnn :: a -> CxtId -> AnnExpr CoreBndr a -> AnnExpr' CoreBndr a
markCxtAnn ann cid expr = AnnLet (AnnNonRec marker (ann, AnnVar cid)) expr
  where
    marker = mkCxtMarkerId (idType cid)

markCxtTagged :: t -> CxtId -> Expr (TaggedBndr t) -> Expr (TaggedBndr t)
markCxtTagged tag cid expr = Let (NonRec (TB marker tag) (Var cid)) expr
  where
    marker = mkCxtMarkerId (idType cid)

markCxtTaggedAnn :: t -> a -> CxtId -> AnnExpr (TaggedBndr t) a
                                    -> AnnExpr' (TaggedBndr t) a
markCxtTaggedAnn tag ann cid expr
  = AnnLet (AnnNonRec (TB marker tag) (ann, AnnVar cid)) expr
  where
    marker = mkCxtMarkerId (idType cid)

removeCxts :: CoreExprWithCxts -> CoreExpr
removeCxts (App fun arg)   = App (removeCxts fun) (removeCxts arg)
removeCxts (Lam bndr body) = Lam bndr (removeCxts body)
removeCxts (Let bind body)
  | isCxtMarker bind       = removeCxts body
  | otherwise              = Let (removeCxtsFromBind bind) (removeCxts body)
removeCxts (Case e b t as) = Case (removeCxts e) b t
                                  [ (con, bndrs, removeCxts rhs)
                                  | (con, bndrs, rhs) <- as ]
removeCxts (Cast expr co)  = Cast (removeCxts expr) co
removeCxts (Tick ti expr)  = Tick ti (removeCxts expr)
removeCxts other           = other

removeCxtsFromBind :: CoreBindWithCxts -> CoreBind
removeCxtsFromBind (NonRec bndr rhs) = NonRec bndr (removeCxts rhs)
removeCxtsFromBind (Rec pairs) = Rec [ (bndr, removeCxts rhs)
                                     | (bndr, rhs) <- pairs ]

--------------------

addCxtsBind :: CoreBind -> UniqSM CoreBindWithCxts
addCxtsBind bind
  = case bind of
      NonRec bndr rhs -> do (bndr', rhs') <- do_pair (bndr, rhs)
                            return $ NonRec bndr' rhs'
      Rec pairs       -> Rec <$> mapM do_pair pairs
  where
    do_pair (bndr, rhs)
      | Just join_arity <- isJoinId_maybe bndr
      , let (bndrs, body) = collectNBinders join_arity rhs
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
  = do cid   <- mkSysLocalM name (exprType expr)
       expr' <- addCxtsExpr expr
       return (markCxt cid expr')

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
