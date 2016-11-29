module CoreArity where

import BasicTypes
import CoreSyn

etaExpandCountingTypes :: JoinArity -> CoreExpr -> CoreExpr