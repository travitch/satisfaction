{-# LANGUAGE DeriveDataTypeable #-}
-- | This constraint enforces that two variables are always assigned
-- the same value.
module Satisfaction.CDCL.Constraint.Equality (
  mkEqualityConstraint
  ) where

import Data.Typeable ( Typeable )

import qualified Data.Ref.Prim as P

import Satisfaction.CDCL.Monad
import qualified Satisfaction.CDCL.Core as C
import qualified Satisfaction.Formula.Literal as L

-- | The constraint data type.  See Note [EqualityRepresentation] for
-- details on how it is handled.
data EqualityConstraint =
  EqualityConstraint { ecActivity :: {-# UNPACK #-} !(P.Ref IO Double)
                     , ecVar1 :: {-# UNPACK #-} !L.Variable
                     , ecVar2 :: {-# UNPACK #-} !L.Variable
                     }
  deriving (Typeable)

instance Eq EqualityConstraint where
  ec1 == ec2 = ecVar1 ec1 == ecVar1 ec2 && ecVar2 ec1 == ecVar2 ec2

-- | Make a new equality constraint between two variables.
mkEqualityConstraint :: L.Variable -> L.Variable -> Solver Constraint
mkEqualityConstraint v1 v2 = do
  r <- P.newRef 0
  let c = EqualityConstraint { ecActivity = r
                             , ecVar1 = v1
                             , ecVar2 = v2
                             }
      con = Constraint equalityInterface c
  C.watchLiteral con (L.toPositiveLiteral v1)
  C.watchLiteral con (L.toNegativeLiteral v1)
  C.watchLiteral con (L.toPositiveLiteral v2)
  C.watchLiteral con (L.toNegativeLiteral v2)
  return con


equalityInterface :: ConstraintInterface EqualityConstraint
equalityInterface = CI { conRemove = eRemove
                       , conPropagate = ePropagate
                       , conSimplify = eSimplify
                       , conReason = eReason
                       , conLocked = eLocked
                       , conReadActivity = eReadActivity
                       , conWriteActivity = eWriteActivity
                       , conAlwaysKeep = eAlwaysKeep
                       }

eAlwaysKeep :: Constraint -> EqualityConstraint -> Solver Bool
eAlwaysKeep _ _ = return True

eWriteActivity :: Constraint -> EqualityConstraint -> Double -> Solver ()
eWriteActivity _ ec a = P.writeRef (ecActivity ec) a

eReadActivity :: Constraint -> EqualityConstraint -> Solver Double
eReadActivity _ ec = P.readRef (ecActivity ec)

-- Since we never remove these (i.e., we always keep them), locked can
-- always return True.  Or False.  It doesn't matter.
eLocked :: Constraint -> EqualityConstraint -> Solver Bool
eLocked _ _ = return True

eSimplify :: Constraint -> EqualityConstraint -> Solver Bool
eSimplify _ _ = return False

eReason :: Constraint -> EqualityConstraint -> Maybe L.Literal -> Solver [L.Literal]
eReason _con ec mlit = do
  bumpActivity ec
  case mlit of
    Nothing -> do
      -- Return the reason that this constraint is conflicting.  That
      -- is going to be the two literals that do not agree (based on
      -- the value of the two variables).
      v1 <- C.variableValue (ecVar1 ec)
      v2 <- C.variableValue (ecVar2 ec)
      return [L.neg (varValLit (ecVar1 ec) v1), L.neg (varValLit (ecVar2 ec) v2)]
    Just lit -> do
      -- This constraint is the reason that 'lit' is True.  We need to
      -- return the literal that implied 'lit'.  That is the other
      -- variable we are watching.  Since this is a bi-implication,
      -- that is just the impliedLiteral.
      return [L.neg (impliedLiteral lit ec)]

varValLit :: L.Variable -> L.Value -> L.Literal
varValLit var val
  | val == L.liftedFalse = L.toNegativeLiteral var
  | val == L.liftedTrue = L.toPositiveLiteral var
  | otherwise = error ("Variable is unassigned in reason computation: " ++ show var)

ePropagate :: Constraint -> EqualityConstraint -> L.Literal -> Solver PropagationResult
ePropagate con ec falseLit = do
  res <- C.tryAssertLiteral (impliedLiteral falseLit ec) (Just con)
  case res of
    True -> return PropagationKeepWatch
    False -> return PropagationConflict

impliedLiteral :: L.Literal -> EqualityConstraint -> L.Literal
impliedLiteral falseLit ec
  | L.isNegated falseLit = L.toNegativeLiteral otherVar
  | otherwise = L.toPositiveLiteral otherVar
  where
    otherVar = if L.var falseLit == ecVar1 ec then ecVar2 ec else ecVar1 ec

eRemove :: Constraint -> EqualityConstraint -> Solver ()
eRemove con ec = do
  C.unwatchLiteral con (L.toPositiveLiteral v1)
  C.unwatchLiteral con (L.toNegativeLiteral v1)
  C.unwatchLiteral con (L.toPositiveLiteral v2)
  C.unwatchLiteral con (L.toNegativeLiteral v2)
  where
    v1 = ecVar1 ec
    v2 = ecVar2 ec

bumpActivity :: EqualityConstraint -> Solver ()
bumpActivity ec = do
  e <- ask
  amount <- P.readRef (eClauseIncrement e)
  act0 <- P.readRef (ecActivity ec)
  let act1 = act0 + amount
  P.writeRef (ecActivity ec) act1
  case act1 > C.activityCap of
    False -> return ()
    True -> C.rescaleActivity

{- Note [EqualityRepresentation]

This constraint covers two variables (v1 and v2) and enforces that
they always have the same value.  To do so, it establishes four
watches:

* l1
* l2
* not l1
* not l2

Whenever any of them is assigned, its propagateUnits implementation
will set the appropriate other value with tryAssertLiteral.  For
example, if l1 becomes False (i.e., 'not l1' is asserted), propagate
will (try to) assert 'not l2'.

This constraint cannot be simplified.

-}
