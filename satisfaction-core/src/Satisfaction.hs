-- | This is the public interface to the Satisfaction SAT solver.
--
-- Problems can be constructed manually or from a simple list-based
-- CNF format.  In the future, more sophisticated problem construction
-- methods will be supported.
--
-- The primary entry points are 'solve', which solves SAT instances
-- with some default parameters, and 'solveWith', which accepts some
-- configuration options.
module Satisfaction (
  solve,
  solveWith,
  Solution(..),
  Model,
  satisfyingAssignment,
  -- * Configuration
  Config,
  defaultConfig,
  setVariableActivityDecayFactor,
  setClauseActivityDecayFactor,
  setMaxLearnedClausesRatio,
  setMaxLearnedClausesAbsolute,
  setMaxLearnedClauseGrowthFactor,
  setMaxConflicts,
  setMaxConflictGrowthFactor,
  -- * Types
  C.CNF,
  C.Lit(..),
  C.fromSimpleList
  ) where

import Satisfaction.Internal.Solver
import qualified Satisfaction.CNF as C
