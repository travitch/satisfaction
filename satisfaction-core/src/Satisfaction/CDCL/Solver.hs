{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
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
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

import Satisfaction.CDCL.Monad
import qualified Satisfaction.CDCL.AnalyzeConflict as AC
import qualified Satisfaction.CDCL.Constraint as CO
import qualified Satisfaction.CDCL.Core as C
import qualified Satisfaction.CDCL.Simplify as SI
import qualified Satisfaction.CDCL.Statistics as ST
import qualified Satisfaction.CDCL.UnitPropagation as P
import qualified Satisfaction.Formula as F
import qualified Satisfaction.Formula.Literal as L
import qualified Satisfaction.Internal.Debug as D

import Prelude

-- | A model of a satisfying assignment
data Model a = Model { modelFormula :: F.CNF a
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

-- | Solve a SAT instance in 'F.CNF' form with the default solver
-- configuration
solve :: Solver ()
      -- ^ Extra assertions to include in the problem
      -> F.CNF a
      -- ^ The formula to solve
      -> IO (Solution a)
solve = solveWith defaultConfig

-- | Solve a SAT instance in 'C.CNF' form with the given 'Config'
solveWith :: Config
          -- ^ Solver configuration
          -> Solver ()
          -- ^ Extra assertions to include in the problem
          -> F.CNF a
          -- ^ The formula to solve
          -> IO (Solution a)
solveWith config extraAssertions cnf = do
  let vrange = F.variableRange cnf
  isol <- runSolver config vrange (extraAssertions >> initializeCNF cnf) $ \hasContradiction -> do
    case hasContradiction of
      True -> unsatisfiable
      False ->
        -- Propagate units based on unit clauses (which have been added to
        -- the propagation queue during setup).  If we already have a
        -- conflict, we are done.  Otherwise, start the decision loop.
        propagateUnits search (const unsatisfiable)
  case isol of
    IUnsat stats -> do
      return Unsatisfiable { solutionStats = stats }
    ISolution assignment stats ->
      return Satisfiable { solutionStats = stats
                         , solutionModel =
                           Model { modelFormula = cnf
                                 , modelRawSolution = assignment
                                 , modelSatisfyingAssignment = F.mapSolution cnf assignment
                                 }
                         }

unsatisfiable :: Solver ISolution
unsatisfiable = IUnsat <$> ST.extractStatistics

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
               -> (Constraint -> Solver ISolution) -- ^ Continuation on conflict
               -> Solver ISolution
propagateUnits kNoConflict kConflict = go
  where
    go = P.withQueuedDecision kNoConflict $ \lit -> do
      liftIO $ D.traceIO ("[pu] Propagating units affected by assignment " ++ show lit)
      P.updateWatchlists lit kConflict unsatisfiable go

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
  dl <- C.getDecisionLevel
  case () of
    _ | dl == 0 -> do
          liftIO $ D.traceIO "[bt] Deriving unsat"
          unsatisfiable
      | otherwise -> do
          -- If we have a special root level (as in minisat), we would want to
          -- use that instead of zero
          C.undoUntil btLevel
          learnClause btLevel assertedLit otherLits
          C.decayVariableActivity
          C.decayClauseActivity
          liftIO $ D.traceIO ("[bt] Learned clause " ++ show (assertedLit : otherLits) ++ " and asserted " ++ show assertedLit)
          kBacktracked

-- | Learn a clause and assert its asserting literal.
--
-- The asserting literal is asserted here.
--
-- If the clause is a singleton, this function simply asserts it.  The
-- decision level should be *ground* if the given clause is a
-- singleton, but this function does not check or enforce that.  The
-- clause learning algorithm should have instructed the backtracking
-- function to backjump appropriately.
--
-- Otherwise, this function simply adds the clause to the list of
-- clauses and sets appropriate watches.  When we construct the
-- learned clause (for non-singleton clauses), the first literal is
-- the asserting literal.  We know we want to watch this literal, so
-- we leave it at index 0.  We need to choose the other literal to
-- watch with 'watchFirstAtLevel'.
--
-- Note that we cannot enforce that learned clause limit here.  We
-- need to at least assert the asserting literal from this clause, but
-- if we do that, we need to have a real clause as its reason.  We
-- cannot say it was a ground literal, since that would mean we could
-- never undo the assignment.  We could, in theory, add a sentinel
-- value that says "this was an asserted literal, but there was no
-- room for its clause", but that is somewhat complicated.  It would
-- also ruin future clause learning involving this literal.  Instead,
-- we'll treat the maximum number of learned clauses as a soft limit
-- and enforce it later (after conflict resolution).
learnClause :: Int -> L.Literal -> [L.Literal] -> Solver ()
learnClause btLevel assertedLit otherLits = do
  e <- ask
  dl <- C.getDecisionLevel
  liftIO $ D.traceIO ("[lc] Learning clause and asserting " ++ show assertedLit ++ " at dl " ++ show dl)
  case otherLits of
    [] -> C.assertLiteral assertedLit Nothing
    (l2:rest) -> do
      P.modifyRef' (eLearnedClauseCount e) (+1)
      con <- CO.mkLearnedClauseConstraint btLevel assertedLit l2 rest
      liftIO $ D.traceIO ("  [lc] Clause ref allocated")
      V.push (eLearnedClauses e) con
      C.assertLiteral assertedLit (Just con)

-- | Traverse a 'C.CNF' problem and assert its clauses as problem
-- clauses.
--
-- Returns 'True' if the problem contains a trivial contradiction
initializeCNF :: F.CNF a -> Solver Bool
initializeCNF cnf = do
  constraints <- asks eProblemClauses
  AT.foldArrayM (watchFirst constraints) False (F.clauseArray cnf)
  where
    watchFirst constraints hasContradiction _ix clause = do
      case F.clauseLiterals clause of
        [] -> return hasContradiction
        l : [] -> do
          validAssertion <- C.tryAssertLiteral l Nothing
          return (hasContradiction || not validAssertion)
        l1 : l2 : rest -> do
          con <- CO.mkClauseConstraint l1 l2 rest
          V.push constraints con
          return hasContradiction

{- Note [Unit Propagation]

There is no explicit propagation queue.  Instead, propagation is based
on the assignment stack, which tracks assignments.  Each literal that
is decided tells us which literals became False (¬Lit).

We are guaranteed that we do not need more storage for the assignment
vector than |vars| because we only decide values for unassigned
variables.

-}
