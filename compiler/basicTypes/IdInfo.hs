{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1993-1998

\section[IdInfo]{@IdInfos@: Non-essential information about @Ids@}

(And a pretty good illustration of quite a few things wrong with
Haskell. [WDP 94/11])
-}

module IdInfo (
        -- * The IdDetails type
        IdDetails(..), pprIdDetails, coVarDetails, isCoVarDetails,
        RecSelParent(..),

        -- * The IdInfo type
        IdInfo,         -- Abstract
        vanillaIdInfo, noCafIdInfo,

        -- ** The OneShotInfo type
        OneShotInfo(..),
        oneShotInfo, noOneShotInfo, hasNoOneShotInfo,
        setOneShotInfo,

        -- ** Zapping various forms of Info
        zapLamInfo, zapFragileInfo,
        zapDemandInfo, zapUsageInfo,

        -- ** The ArityInfo type
        ArityInfo,
        unknownArity,
        arityInfo, setArityInfo, ppArityInfo,

        callArityInfo, setCallArityInfo,

        -- ** Demand and strictness Info
        strictnessInfo, setStrictnessInfo,
        demandInfo, setDemandInfo, pprStrictness,

        -- ** Join point flag
        JoinPointInfo(..),
        joinPointInfo, setJoinPointInfo,
        noJoinPointInfo, ppJoinPointInfo,

        -- ** Unfolding Info
        unfoldingInfo, setUnfoldingInfo, setUnfoldingInfoLazily,

        -- ** The InlinePragInfo type
        InlinePragInfo,
        inlinePragInfo, setInlinePragInfo,

        -- ** The OccInfo type
        OccInfo(..),
        isDeadOcc, isStrongLoopBreaker, isWeakLoopBreaker,
        occInfo, setOccInfo,

        InsideLam, OneBranch,
        insideLam, notInsideLam, oneBranch, notOneBranch,

        -- ** The RuleInfo type
        RuleInfo(..),
        emptyRuleInfo,
        isEmptyRuleInfo, ruleInfoFreeVars,
        ruleInfoRules, setRuleInfoHead,
        ruleInfo, setRuleInfo,

        -- ** The CAFInfo type
        CafInfo(..),
        ppCafInfo, mayHaveCafRefs,
        cafInfo, setCafInfo,

        -- ** Tick-box Info
        TickBoxOp(..), TickBoxId,
    ) where

import CoreSyn

import Class
import {-# SOURCE #-} PrimOp (PrimOp)
import Name
import VarSet
import BasicTypes
import DataCon
import TyCon
import {-# SOURCE #-} PatSyn
import ForeignCall
import Outputable
import Module
import Demand

-- infixl so you can say (id `set` a `set` b)
infixl  1 `setRuleInfo`,
          `setArityInfo`,
          `setInlinePragInfo`,
          `setUnfoldingInfo`,
          `setOneShotInfo`,
          `setOccInfo`,
          `setCafInfo`,
          `setStrictnessInfo`,
          `setDemandInfo`

{-
************************************************************************
*                                                                      *
                     IdDetails
*                                                                      *
************************************************************************
-}

-- | The 'IdDetails' of an 'Id' give stable, and necessary,
-- information about the Id.
data IdDetails
  = VanillaId

  -- | The 'Id' for a record selector
  | RecSelId
    { sel_tycon   :: RecSelParent
    , sel_naughty :: Bool       -- True <=> a "naughty" selector which can't actually exist, for example @x@ in:
                                --    data T = forall a. MkT { x :: a }
    }                           -- See Note [Naughty record selectors] in TcTyClsDecls

  | DataConWorkId DataCon       -- ^ The 'Id' is for a data constructor /worker/
  | DataConWrapId DataCon       -- ^ The 'Id' is for a data constructor /wrapper/

                                -- [the only reasons we need to know is so that
                                --  a) to support isImplicitId
                                --  b) when desugaring a RecordCon we can get
                                --     from the Id back to the data con]
  | ClassOpId Class             -- ^ The 'Id' is a superclass selector,
                                -- or class operation of a class

  | PrimOpId PrimOp             -- ^ The 'Id' is for a primitive operator
  | FCallId ForeignCall         -- ^ The 'Id' is for a foreign call

  | TickBoxOpId TickBoxOp       -- ^ The 'Id' is for a HPC tick box (both traditional and binary)

  | DFunId Bool                 -- ^ A dictionary function.
       -- Bool = True <=> the class has only one method, so may be
       --                  implemented with a newtype, so it might be bad
       --                  to be strict on this dictionary

  | CoVarId                    -- ^ A coercion variable

data RecSelParent = RecSelData TyCon | RecSelPatSyn PatSyn deriving Eq
  -- Either `TyCon` or `PatSyn` depending
  -- on the origin of the record selector.
  -- For a data type family, this is the
  -- /instance/ 'TyCon' not the family 'TyCon'

instance Outputable RecSelParent where
  ppr p = case p of
            RecSelData ty_con -> ppr ty_con
            RecSelPatSyn ps   -> ppr ps

-- | Just a synonym for 'CoVarId'. Written separately so it can be
-- exported in the hs-boot file.
coVarDetails :: IdDetails
coVarDetails = CoVarId

-- | Check if an 'IdDetails' says 'CoVarId'.
isCoVarDetails :: IdDetails -> Bool
isCoVarDetails CoVarId = True
isCoVarDetails _       = False

instance Outputable IdDetails where
    ppr = pprIdDetails

pprIdDetails :: IdDetails -> SDoc
pprIdDetails VanillaId = empty
pprIdDetails other     = brackets (pp other)
 where
   pp VanillaId         = panic "pprIdDetails"
   pp (DataConWorkId _) = text "DataCon"
   pp (DataConWrapId _) = text "DataConWrapper"
   pp (ClassOpId {})    = text "ClassOp"
   pp (PrimOpId _)      = text "PrimOp"
   pp (FCallId _)       = text "ForeignCall"
   pp (TickBoxOpId _)   = text "TickBoxOp"
   pp (DFunId nt)       = text "DFunId" <> ppWhen nt (text "(nt)")
   pp (RecSelId { sel_naughty = is_naughty })
                         = brackets $ text "RecSel"
                            <> ppWhen is_naughty (text "(naughty)")
   pp CoVarId           = text "CoVarId"

{-
************************************************************************
*                                                                      *
\subsection{The main IdInfo type}
*                                                                      *
************************************************************************
-}

-- | An 'IdInfo' gives /optional/ information about an 'Id'.  If
-- present it never lies, but it may not be present, in which case there
-- is always a conservative assumption which can be made.
--
-- Two 'Id's may have different info even though they have the same
-- 'Unique' (and are hence the same 'Id'); for example, one might lack
-- the properties attached to the other.
--
-- Much of the 'IdInfo' gives information about the value, or definition, of
-- the 'Id', independent of its usage. Exceptions to this
-- are 'demandInfo', 'occInfo', 'oneShotInfo', 'callArityInfo' and
-- 'joinPointInfo'.
data IdInfo
  = IdInfo {
        arityInfo       :: !ArityInfo,          -- ^ 'Id' arity
        ruleInfo        :: RuleInfo,            -- ^ Specialisations of the 'Id's function which exist
                                                -- See Note [Specialisations and RULES in IdInfo]
        unfoldingInfo   :: Unfolding,           -- ^ The 'Id's unfolding
        cafInfo         :: CafInfo,             -- ^ 'Id' CAF info
        oneShotInfo     :: OneShotInfo,         -- ^ Info about a lambda-bound variable, if the 'Id' is one
        inlinePragInfo  :: InlinePragma,        -- ^ Any inline pragma atached to the 'Id'
        occInfo         :: OccInfo,             -- ^ How the 'Id' occurs in the program

        strictnessInfo  :: StrictSig,      --  ^ A strictness signature

        demandInfo      :: Demand,       -- ^ ID demand information
        callArityInfo   :: !ArityInfo,   -- ^ How this is called.
                                         -- n <=> all calls have at least n arguments
        joinPointInfo   :: JoinPointInfo -- ^ Is the 'Id' a join point?
    }

-- Setters

setRuleInfo :: IdInfo -> RuleInfo -> IdInfo
setRuleInfo       info sp = sp `seq` info { ruleInfo = sp }
setInlinePragInfo :: IdInfo -> InlinePragma -> IdInfo
setInlinePragInfo info pr = pr `seq` info { inlinePragInfo = pr }
setOccInfo :: IdInfo -> OccInfo -> IdInfo
setOccInfo        info oc = oc `seq` info { occInfo = oc }
        -- Try to avoid spack leaks by seq'ing

setUnfoldingInfoLazily :: IdInfo -> Unfolding -> IdInfo
setUnfoldingInfoLazily info uf  -- Lazy variant to avoid looking at the
  =                             -- unfolding of an imported Id unless necessary
    info { unfoldingInfo = uf } -- (In this case the demand-zapping is redundant.)

setUnfoldingInfo :: IdInfo -> Unfolding -> IdInfo
setUnfoldingInfo info uf
  = -- We don't seq the unfolding, as we generate intermediate
    -- unfoldings which are just thrown away, so evaluating them is a
    -- waste of time.
    -- seqUnfolding uf `seq`
    info { unfoldingInfo = uf }

setArityInfo :: IdInfo -> ArityInfo -> IdInfo
setArityInfo      info ar  = info { arityInfo = ar  }
setCallArityInfo :: IdInfo -> ArityInfo -> IdInfo
setCallArityInfo info ar  = info { callArityInfo = ar  }
setCafInfo :: IdInfo -> CafInfo -> IdInfo
setCafInfo        info caf = info { cafInfo = caf }

setOneShotInfo :: IdInfo -> OneShotInfo -> IdInfo
setOneShotInfo      info lb = {-lb `seq`-} info { oneShotInfo = lb }

setDemandInfo :: IdInfo -> Demand -> IdInfo
setDemandInfo info dd = dd `seq` info { demandInfo = dd }

setStrictnessInfo :: IdInfo -> StrictSig -> IdInfo
setStrictnessInfo info dd = dd `seq` info { strictnessInfo = dd }

setJoinPointInfo :: IdInfo -> JoinPointInfo -> IdInfo
setJoinPointInfo info jp = jp `seq` info { joinPointInfo = jp }

-- | Basic 'IdInfo' that carries no useful information whatsoever
vanillaIdInfo :: IdInfo
vanillaIdInfo
  = IdInfo {
            cafInfo             = vanillaCafInfo,
            arityInfo           = unknownArity,
            ruleInfo            = emptyRuleInfo,
            unfoldingInfo       = noUnfolding,
            oneShotInfo         = NoOneShotInfo,
            inlinePragInfo      = defaultInlinePragma,
            occInfo             = NoOccInfo,
            demandInfo          = topDmd,
            strictnessInfo      = nopSig,
            callArityInfo       = unknownArity,
            joinPointInfo       = noJoinPointInfo
           }

-- | More informative 'IdInfo' we can use when we know the 'Id' has no CAF references
noCafIdInfo :: IdInfo
noCafIdInfo  = vanillaIdInfo `setCafInfo`    NoCafRefs
        -- Used for built-in type Ids in MkId.

{-
************************************************************************
*                                                                      *
\subsection[arity-IdInfo]{Arity info about an @Id@}
*                                                                      *
************************************************************************

For locally-defined Ids, the code generator maintains its own notion
of their arities; so it should not be asking...  (but other things
besides the code-generator need arity info!)
-}

-- | An 'ArityInfo' of @n@ tells us that partial application of this
-- 'Id' to up to @n-1@ value arguments does essentially no work.
--
-- That is not necessarily the same as saying that it has @n@ leading
-- lambdas, because coerces may get in the way.
--
-- The arity might increase later in the compilation process, if
-- an extra lambda floats up to the binding site.
type ArityInfo = Arity

-- | It is always safe to assume that an 'Id' has an arity of 0
unknownArity :: Arity
unknownArity = 0 :: Arity

ppArityInfo :: Int -> SDoc
ppArityInfo 0 = empty
ppArityInfo n = hsep [text "Arity", int n]

{-
************************************************************************
*                                                                      *
\subsection[joinPoint-IdInfo]{Join point flag on @Id@}
*                                                                      *
************************************************************************

In Core, a *join point* is a function whose only occurrences are
saturated tail calls. A *tail call* is an invocation in a *tail
context*, which is a context conforming to the following grammar:

  T ::= []
     |  let ... in T
     |  let <join> k = T; ... in ...
     |  case ... of P -> T; ...

The invariant on a join point, then, is that given an expression

  let join k = ... in E,
  
any occurrence of k "factors" E into T[k E1 ... En], where T is a tail
context and n is k's arity. (Recursive invocations are also okay, subject to
the same restriction.) Only local variables can be join points.

Note from the above grammar that one join point can invoke another from an
outer scope, but a non-join-point cannot:

  let <join> k = \n m -> ...
      <join> h = \n -> k n n -- GOOD
             f = \n -> k n n -- BAD
  in case b of True  -> h 3
               False -> 1 + f 4

Here f is not a join point since it has a non-tail call in the False branch;
thus it should not invoke k.

Join points are very special: At runtime, they exist only as blocks of code, so
they are never allocated and invoking them is very fast (little more than a
jump). Thus we would like to maintain their status as join points when possible.
However, it is always safe to set the join point flag to False.
-}

-- | Whether an 'Id' is a *join point,* as determined by its occurrences. A
-- join point only occurs as a saturated tail call, such that no closure is
-- needed and invocation can be "by goto."
data JoinPointInfo = JoinPoint | NotJoinPoint deriving (Eq)

-- | It is always safe to assume that a function is not a join point
noJoinPointInfo :: JoinPointInfo
noJoinPointInfo = NotJoinPoint

ppJoinPointInfo :: JoinPointInfo -> SDoc
ppJoinPointInfo NotJoinPoint = empty
ppJoinPointInfo JoinPoint = text "Join"

{-
************************************************************************
*                                                                      *
\subsection{Inline-pragma information}
*                                                                      *
************************************************************************
-}

-- | Tells when the inlining is active.
-- When it is active the thing may be inlined, depending on how
-- big it is.
--
-- If there was an @INLINE@ pragma, then as a separate matter, the
-- RHS will have been made to look small with a Core inline 'Note'
--
-- The default 'InlinePragInfo' is 'AlwaysActive', so the info serves
-- entirely as a way to inhibit inlining until we want it
type InlinePragInfo = InlinePragma

{-
************************************************************************
*                                                                      *
               Strictness
*                                                                      *
************************************************************************
-}

pprStrictness :: StrictSig -> SDoc
pprStrictness sig = ppr sig

{-
************************************************************************
*                                                                      *
        RuleInfo
*                                                                      *
************************************************************************

Note [Specialisations and RULES in IdInfo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Generally speaking, a GlobalId has an *empty* RuleInfo.  All their
RULES are contained in the globally-built rule-base.  In principle,
one could attach the to M.f the RULES for M.f that are defined in M.
But we don't do that for instance declarations and so we just treat
them all uniformly.

The EXCEPTION is PrimOpIds, which do have rules in their IdInfo. That is
jsut for convenience really.

However, LocalIds may have non-empty RuleInfo.  We treat them
differently because:
  a) they might be nested, in which case a global table won't work
  b) the RULE might mention free variables, which we use to keep things alive

In TidyPgm, when the LocalId becomes a GlobalId, its RULES are stripped off
and put in the global list.
-}

-- | Records the specializations of this 'Id' that we know about
-- in the form of rewrite 'CoreRule's that target them
data RuleInfo
  = RuleInfo
        [CoreRule]
        DVarSet         -- Locally-defined free vars of *both* LHS and RHS
                        -- of rules.  I don't think it needs to include the
                        -- ru_fn though.
                        -- Note [Rule dependency info] in OccurAnal

-- | Assume that no specilizations exist: always safe
emptyRuleInfo :: RuleInfo
emptyRuleInfo = RuleInfo [] emptyDVarSet

isEmptyRuleInfo :: RuleInfo -> Bool
isEmptyRuleInfo (RuleInfo rs _) = null rs

-- | Retrieve the locally-defined free variables of both the left and
-- right hand sides of the specialization rules
ruleInfoFreeVars :: RuleInfo -> DVarSet
ruleInfoFreeVars (RuleInfo _ fvs) = fvs

ruleInfoRules :: RuleInfo -> [CoreRule]
ruleInfoRules (RuleInfo rules _) = rules

-- | Change the name of the function the rule is keyed on on all of the 'CoreRule's
setRuleInfoHead :: Name -> RuleInfo -> RuleInfo
setRuleInfoHead fn (RuleInfo rules fvs)
  = RuleInfo (map (setRuleIdName fn) rules) fvs

{-
************************************************************************
*                                                                      *
\subsection[CG-IdInfo]{Code generator-related information}
*                                                                      *
************************************************************************
-}

-- CafInfo is used to build Static Reference Tables (see simplStg/SRT.hs).

-- | Records whether an 'Id' makes Constant Applicative Form references
data CafInfo
        = MayHaveCafRefs                -- ^ Indicates that the 'Id' is for either:
                                        --
                                        -- 1. A function or static constructor
                                        --    that refers to one or more CAFs, or
                                        --
                                        -- 2. A real live CAF

        | NoCafRefs                     -- ^ A function or static constructor
                                        -- that refers to no CAFs.
        deriving (Eq, Ord)

-- | Assumes that the 'Id' has CAF references: definitely safe
vanillaCafInfo :: CafInfo
vanillaCafInfo = MayHaveCafRefs

mayHaveCafRefs :: CafInfo -> Bool
mayHaveCafRefs  MayHaveCafRefs = True
mayHaveCafRefs _               = False

instance Outputable CafInfo where
   ppr = ppCafInfo

ppCafInfo :: CafInfo -> SDoc
ppCafInfo NoCafRefs = text "NoCafRefs"
ppCafInfo MayHaveCafRefs = empty

{-
************************************************************************
*                                                                      *
\subsection{Bulk operations on IdInfo}
*                                                                      *
************************************************************************
-}

-- | This is used to remove information on lambda binders that we have
-- setup as part of a lambda group, assuming they will be applied all at once,
-- but turn out to be part of an unsaturated lambda as in e.g:
--
-- > (\x1. \x2. e) arg1
zapLamInfo :: IdInfo -> Maybe IdInfo
zapLamInfo info@(IdInfo {occInfo = occ, demandInfo = demand})
  | is_safe_occ occ && is_safe_dmd demand
  = Nothing
  | otherwise
  = Just (info {occInfo = safe_occ, demandInfo = topDmd})
  where
        -- The "unsafe" occ info is the ones that say I'm not in a lambda
        -- because that might not be true for an unsaturated lambda
    is_safe_occ (OneOcc in_lam _ _) = in_lam
    is_safe_occ _other              = True

    safe_occ = case occ of
                 OneOcc _ once int_cxt -> OneOcc insideLam once int_cxt
                 _other                -> occ

    is_safe_dmd dmd = not (isStrictDmd dmd)

-- | Remove all demand info on the 'IdInfo'
zapDemandInfo :: IdInfo -> Maybe IdInfo
zapDemandInfo info = Just (info {demandInfo = topDmd})

-- | Remove usage (but not strictness) info on the 'IdInfo'
zapUsageInfo :: IdInfo -> Maybe IdInfo
zapUsageInfo info = Just (info {demandInfo = zapUsageDemand (demandInfo info)})

zapFragileInfo :: IdInfo -> Maybe IdInfo
-- ^ Zap info that depends on free variables
zapFragileInfo info
  = Just (info `setRuleInfo` emptyRuleInfo
               `setUnfoldingInfo` noUnfolding
               `setOccInfo` zapFragileOcc occ)
  where
    occ = occInfo info

{-
************************************************************************
*                                                                      *
\subsection{TickBoxOp}
*                                                                      *
************************************************************************
-}

type TickBoxId = Int

-- | Tick box for Hpc-style coverage
data TickBoxOp
   = TickBox Module {-# UNPACK #-} !TickBoxId

instance Outputable TickBoxOp where
    ppr (TickBox mod n)         = text "tick" <+> ppr (mod,n)
