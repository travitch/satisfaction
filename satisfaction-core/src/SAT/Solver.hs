{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
module SAT.Solver (
  solve,
  nextSolution,
  Solution,
  satisfyingAssignment,
  C.CNF,
  C.Lit(..),
  C.fromSimpleList
  ) where

import Control.Applicative
import qualified Data.Array.Prim.Unboxed as PUA

import qualified SAT.CNF as C
import qualified SAT.Literal as L
import SAT.Solver.Monad
import qualified SAT.Solver.Debug as D

data Solution a = Solution { _solutionFormula :: C.CNF a
                           , _rawSolution :: AnAssignment
                           , satisfyingAssignment :: [(a, Bool)]
                           }
                deriving (Eq, Ord, Show)

data ISolution = IUnsat
               | ISolution AnAssignment

type AnAssignment = PUA.Array L.Variable L.Value

solve :: C.CNF a -> IO (Maybe (Solution a))
solve cnf = do
  isol <- runSolver cnf $ do
    -- Propagate units based on unit clauses (which have been added to
    -- the propagation queue during setup).  If we already have a
    -- conflict, we are done.  Otherwise, start the decision loop.
    propagateUnits go (\_ -> return IUnsat)
  case isol of
    IUnsat -> return Nothing
    ISolution assignment ->
      return $ Just Solution { _solutionFormula = cnf
                             , _rawSolution = assignment
                             , satisfyingAssignment = C.mapSolution cnf assignment
                             }
  where
    go = decide (propagateUnits go (backtrack go))

-- | Find the next solution in the search space, if any.
nextSolution :: Solution a -> IO (Maybe (Solution a))
nextSolution = undefined

-- | Inspect the current state of the solver and produce a solution.
--
-- This needs to preserve all of the state so that we can pick up the
-- search at the same spot.
extractSolution :: Solver ISolution
extractSolution = ISolution <$> extractAssignment

-- | Drain the propagation queue, reassigning watched variables as
-- needed.  If a clause has become unit (i.e., all literals are false
-- but one unassigned), add the relevant variable to the propagation
-- queue.  If we encounter a conflict, call the conflict continuation.
--
-- The polarity array lets us track what value each of the units we
-- propagate will need its variable to be assigned to.  We use this to
-- detect conflicts between unit clauses early before we actually do
-- the assignment.
propagateUnits :: Solver ISolution               -- ^ Continuation if there was no conflict after propagating
               -> (Conflict -> Solver ISolution) -- ^ Continuation on conflict
               -> Solver ISolution
propagateUnits kNoConflict kConflict = go
  where
    go = withQueuedDecision kNoConflict $ \lit -> do
      liftIO $ D.traceIO ("[pu] Propagating units affected by assignment " ++ show lit)
      updateWatchlists lit kConflict go
{-# INLINE propagateUnits #-}

-- | Assign a value to the next unassigned 'Variable'.
--
-- If there are no more variables to assign, extract a solution from
-- the current solver state and return it.
decide :: Solver ISolution -> Solver ISolution
decide kAssigned =
  withNextDecidedLiteral extractSolution $ \lit -> do
    liftIO $ D.traceIO ("[d] Asserting " ++ show lit)
    incrementDecisionLevel
    assertLiteral lit
    kAssigned
{-# INLINE decide #-}

-- | Backtrack (based on the current decision level)
--
-- Undo the assignments of all of the variables in the current
-- decision level.  If we hit decision level zero (top level unit
-- clauses), return Unsat.
--
-- The conflict that caused the backtrack is given as an input so it
-- can be analyzed; it may let us backjump more than one variable.
backtrack :: Solver ISolution -- ^ Continuation on a successful backtrack
          -> Conflict
          -> Solver ISolution
backtrack kBacktracked _conflict = go
  where
    go = do
      dl <- getDecisionLevel
      liftIO $ D.traceIO ("[bt] Backtracking to decision level " ++ show dl)
      case () of
        _ | dl == 0 -> return IUnsat
          | otherwise -> do
              undoDecisionLevel (return IUnsat) kBacktracked $ \lit -> do
                liftIO $ D.traceIO ("  [bt] Undoing assignment to " ++ show (L.var lit))
                resetVariable (L.var lit)
--                assignVariableValue (L.var lit) L.unassigned L.triedNothing
--              kBacktracked
{-# INLINE backtrack #-}

{- Note [Unit Propagation]

There is no explicit propagation queue.  Instead, propagation is based
on the assignment stack, which tracks assignments.  Each literal that
is decided tells us which literals became False (¬Lit).

We are guaranteed that we do not need more storage for the assignment
vector than |vars| because we only decide values for unassigned
variables.

-}
