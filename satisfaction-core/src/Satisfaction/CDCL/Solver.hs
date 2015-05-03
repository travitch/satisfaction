{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
module Satisfaction.CDCL.Solver (
  solve,
  solveWith,
  nextSolution,
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
  -- Types and accessors
  Solution(..),
  Model,
  satisfyingAssignment,
  ) where

import Control.Applicative
import qualified Data.Array.Prim.Unboxed as PUA

import Satisfaction.CDCL.Monad
import qualified Satisfaction.CDCL.AnalyzeConflict as AC
import qualified Satisfaction.CDCL.Clause as CL
import qualified Satisfaction.CDCL.Core as C
import qualified Satisfaction.CDCL.Simplify as SI
import qualified Satisfaction.CDCL.Statistics as ST
import qualified Satisfaction.CDCL.UnitPropagation as P
import qualified Satisfaction.Formula.CNF as C
import qualified Satisfaction.Formula.Literal as L
import qualified Satisfaction.Internal.Debug as D

import Prelude

-- | A model of a satisfying assignment
data Model a = Model { modelFormula :: C.CNF a
                     , modelRawSolution :: PUA.Array L.Variable L.Value
                     , modelSatisfyingAssignment :: [(a, Bool)]
                     }
               deriving (Show)

-- | The solution to a SAT instance; either 'Unsatisfiable' or
-- 'Satisfiable' with a 'Model'.
--
-- The solution also contains statistics gathered by the solver.
data Solution a = Satisfiable { solutionStats :: ST.Statistics
                              , solutionModel :: Model a
                              }
                | Unsatisfiable { solutionStats :: ST.Statistics }
                deriving (Show)

data ISolution = IUnsat ST.Statistics
               | ISolution (PUA.Array L.Variable L.Value) ST.Statistics

-- | A default solver configuration that should be reasonable for many
-- problems
defaultConfig :: Config
defaultConfig = Config { cVariableActivityDecayFactor = 0.95
                       , cClauseActivityDecayFactor = 0.999
                       , cMaxLearnedClauses = LLRelativeRatio 0.333
                       , cMaxLearnedClauseGrowthFactor = 1.1
                       , cMaxConflicts = 100
                       , cMaxConflictGrowthFactor = 1.5
                       }

-- | Set the (initial) maximum number of conflicts allowed before the
-- search restarts.
--
-- The maximum number of conflicts is increased after each restart.
-- If it is -1, the search will never restart.
--
-- Default value: 100
setMaxConflicts :: Int -> Config -> Config
setMaxConflicts i cfg = cfg { cMaxConflicts = i }

-- | Set the multiplier used to increase the maximum number of
-- conflicts after each restart.
--
-- This value should be greater than 1.
--
-- Default: 1.5
setMaxConflictGrowthFactor :: Double -> Config -> Config
setMaxConflictGrowthFactor f cfg =
  cfg { cMaxConflictGrowthFactor = f }

-- | Increase the number of allowed learned clauses by this factor
-- each restart.  This should be greater than 1.
--
-- Default: 1.1
setMaxLearnedClauseGrowthFactor :: Double -> Config -> Config
setMaxLearnedClauseGrowthFactor f cfg =
  cfg { cMaxLearnedClauseGrowthFactor = f }

-- | The amount by which to decay the variable activity increment after each
-- conflict.  It should be in the range (0, 1).
--
-- Default: 0.95
setVariableActivityDecayFactor :: Double -> Config -> Config
setVariableActivityDecayFactor i cfg =
  cfg { cVariableActivityDecayFactor = i }

-- | The amount by which to decay the clause activity after each
-- conflict.  It should be in the range (0, 1).
--
-- Default: 0.999
setClauseActivityDecayFactor :: Double -> Config -> Config
setClauseActivityDecayFactor i cfg =
  cfg { cClauseActivityDecayFactor = i }

-- | Set the (initial) maximum number of learned clauses to a *ratio*
-- of the number of problem clauses.
--
-- Default: 0.333
setMaxLearnedClausesRatio :: Double -> Config -> Config
setMaxLearnedClausesRatio r cfg =
  cfg { cMaxLearnedClauses = LLRelativeRatio r }

-- | Set the (initial) maximum number of learned clauses to an
-- integral value.  This is exclusive with
-- 'setMaxLearnedClausesRatio', which is the default.
setMaxLearnedClausesAbsolute :: Int -> Config -> Config
setMaxLearnedClausesAbsolute i cfg =
  cfg { cMaxLearnedClauses = LLAbsolute i }

-- | Solve a SAT instance in 'C.CNF' form with the default solver
-- configuration
solve :: C.CNF a -> IO (Solution a)
solve = solveWith defaultConfig

-- | Solve a SAT instance in 'C.CNF' form with the given 'Config'
solveWith :: Config -> C.CNF a -> IO (Solution a)
solveWith config cnf = do
  isol <- runSolver config cnf $ \hasContradiction -> do
    case hasContradiction of
      True -> IUnsat <$> ST.extractStatistics
      False ->
        -- Propagate units based on unit clauses (which have been added to
        -- the propagation queue during setup).  If we already have a
        -- conflict, we are done.  Otherwise, start the decision loop.
        propagateUnits search (\_ -> IUnsat <$> ST.extractStatistics)
  case isol of
    IUnsat stats -> do
      return Unsatisfiable { solutionStats = stats }
    ISolution assignment stats ->
      return Satisfiable { solutionStats = stats
                         , solutionModel =
                           Model { modelFormula = cnf
                                 , modelRawSolution = assignment
                                 , modelSatisfyingAssignment = C.mapSolution cnf assignment
                                 }
                         }

-- | Extract a satisfying assignment from the model.
satisfyingAssignment :: Model a -> [(a, Bool)]
satisfyingAssignment = modelSatisfyingAssignment

search :: Solver ISolution
search = go
  where
    go = decide (propagateUnits go (AC.analyzeConflict (backtrack afterBacktrack)))
    afterBacktrack = propagateUnits go (AC.analyzeConflict (backtrack afterBacktrack))

-- | Find the next solution in the search space, if any.
nextSolution :: Solution a -> IO (Solution a)
nextSolution = undefined

-- | Inspect the current state of the solver and produce a solution.
--
-- This needs to preserve all of the state so that we can pick up the
-- search at the same spot.
extractSolution :: Solver ISolution
extractSolution = ISolution <$> C.extractAssignment <*> ST.extractStatistics

-- | Drain the propagation queue, reassigning watched variables as
-- needed.  If a clause has become unit (i.e., all literals are false
-- but one unassigned), add the relevant variable to the propagation
-- queue.  If we encounter a conflict, call the conflict continuation.
--
-- The polarity array lets us track what value each of the units we
-- propagate will need its variable to be assigned to.  We use this to
-- detect conflicts between unit clauses early before we actually do
-- the assignment.
propagateUnits :: Solver ISolution                -- ^ Continuation if there was no conflict after propagating
               -> (CL.Clause Solver -> Solver ISolution) -- ^ Continuation on conflict
               -> Solver ISolution
propagateUnits kNoConflict kConflict = go
  where
    go = P.withQueuedDecision kNoConflict $ \lit -> do
      liftIO $ D.traceIO ("[pu] Propagating units affected by assignment " ++ show lit)
      P.updateWatchlists lit kConflict (IUnsat <$> ST.extractStatistics) go

-- | Assign a value to the next unassigned 'Variable'.
--
-- If there are no more variables to assign, extract a solution from
-- the current solver state and return it.
decide :: Solver ISolution -> Solver ISolution
decide kAssigned = do
  SI.reduceLearnedClauses
  SI.simplifyClauses
  C.restartWith search $ C.withNextDecidedLiteral extractSolution $ \lit -> do
    liftIO $ D.traceIO ("[d] Asserting " ++ show lit)
    C.incrementDecisionLevel
    C.assertLiteral lit Nothing
    kAssigned

-- | Backtrack (based on the current decision level)
--
-- Undo the assignments of all of the variables in the current
-- decision level.  If we hit decision level zero (top level unit
-- clauses), return Unsat.
--
-- The conflict that caused the backtrack is given as an input so it
-- can be analyzed; it may let us backjump more than one variable.
backtrack :: Solver ISolution -- ^ Continuation on a successful backtrack
          -> AC.Conflict
          -> Solver ISolution
backtrack kBacktracked AC.Conflict { AC.cAssertingLit = assertedLit
                                   , AC.cOtherLits = otherLits
                                   , AC.cBacktrackLevel = btLevel
                                   } = do
  liftIO $ D.traceIO ("[bt] Backtracking due to conflict " ++ show (assertedLit : otherLits) ++ " to " ++ show btLevel)
  dl <- getDecisionLevel
  case () of
    _ | dl == 0 -> do
          liftIO $ D.traceIO "[bt] Deriving unsat"
          IUnsat <$> ST.extractStatistics
      | otherwise -> do
          -- If we have a special root level (as in minisat), we would want to
          -- use that instead of zero
          C.undoUntil btLevel
          C.learnClause btLevel assertedLit otherLits
          C.decayVariableActivity
          C.decayClauseActivity
          liftIO $ D.traceIO ("[bt] Learned clause " ++ show (assertedLit : otherLits) ++ " and asserted " ++ show assertedLit)
          kBacktracked

{- Note [Unit Propagation]

There is no explicit propagation queue.  Instead, propagation is based
on the assignment stack, which tracks assignments.  Each literal that
is decided tells us which literals became False (¬Lit).

We are guaranteed that we do not need more storage for the assignment
vector than |vars| because we only decide values for unassigned
variables.

-}
