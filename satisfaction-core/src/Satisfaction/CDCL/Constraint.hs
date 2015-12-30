-- | This module defines generalized 'Constraint's
--
-- Clauses are one type of constraint and can implement this
-- interface.  Other constraints might include equality constraints
-- between variables or "M-of-N" style constraints.
module Satisfaction.CDCL.Constraint (
  -- * Constraint constructors
  mkClauseConstraint,
  mkLearnedClauseConstraint,
  mkEqualityConstraint,
  -- * Constraint helpers
  constraintCalculateConflictReason,
  constraintReadActivity,
  constraintAlwaysKeep,
  constraintRemove,
  constraintSimplify,
  constraintPropagate,
  constraintIsLocked
  ) where

import qualified Satisfaction.Formula.Literal as L
import Satisfaction.CDCL.Monad
import Satisfaction.CDCL.Constraint.Clause ( mkClauseConstraint, mkLearnedClauseConstraint )
import Satisfaction.CDCL.Constraint.Equality ( mkEqualityConstraint )


-- | Perform propagation for this literal that was detected to be
-- False.
--
-- Return 'False' if the propagation detected a conflict.
constraintPropagate :: Constraint -> L.Literal -> Solver PropagationResult
constraintPropagate con@(Constraint CI { conPropagate = f } v) l = f con v l
{-# INLINE constraintPropagate #-}

constraintSimplify :: Constraint -> Solver Bool
constraintSimplify con@(Constraint CI { conSimplify = f } v) = f con v
{-# INLINE constraintSimplify #-}

constraintCalculateConflictReason :: Constraint -> Maybe L.Literal -> Solver [L.Literal]
constraintCalculateConflictReason con@(Constraint CI { conReason = f } v) p = f con v p
{-# INLINE constraintCalculateConflictReason #-}

constraintIsLocked :: Constraint -> Solver Bool
constraintIsLocked con@(Constraint CI { conLocked = f } v) = f con v
{-# INLINE constraintIsLocked #-}

constraintReadActivity :: Constraint -> Solver Double
constraintReadActivity con@(Constraint CI { conReadActivity = f } v) = f con v
{-# INLINE constraintReadActivity #-}

-- | Return 'True' if the simplifier should never throw away this
-- constraint.
constraintAlwaysKeep :: Constraint -> Solver Bool
constraintAlwaysKeep con@(Constraint CI { conAlwaysKeep = f } v) = f con v
{-# INLINE constraintAlwaysKeep #-}

constraintRemove :: Constraint -> Solver ()
constraintRemove con@(Constraint CI { conRemove = f } v) = f con v
{-# INLINE constraintRemove #-}
