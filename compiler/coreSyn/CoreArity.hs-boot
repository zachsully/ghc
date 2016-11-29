module CoreArity where

import BasicTypes
import CoreSyn

splitJoinPoint :: JoinArity -> CoreExpr -> ([CoreBndr], CoreExpr)
