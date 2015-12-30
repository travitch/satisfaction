{-# LANGUAGE FlexibleContexts #-}
-- | Functions for unit propagation using two-watched literals
module Satisfaction.CDCL.UnitPropagation (
  withQueuedDecision,
  updateWatchlists
  ) where

import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

import Satisfaction.CDCL.Monad
import qualified Satisfaction.CDCL.Core as C
import qualified Satisfaction.CDCL.Constraint as CO
import qualified Satisfaction.Formula.Literal as L
import qualified Satisfaction.Internal.Debug as D

-- | For the next 'Literal' that has been decided in the queue, call
-- the given continuation.  If there are no more literals in the
-- queue, call the empty queue continuation.
--
-- The queue is embedded in the decision stack.  'ePropagationQueue'
-- points to the next literal in the queue.  Before we pass a literal
-- to the continuation, we have to advance the queue pointer.
withQueuedDecision :: Solver a                -- ^ Called when the queue is empty
                   -> (L.Literal -> Solver a) -- ^ Called on each 'Literal' in the queue
                   -> Solver a
withQueuedDecision kEmpty kProp = do
  e <- ask
  let dvec = eDecisionStack e
      qref = ePropagationQueue e
  decisionIndex <- P.readRef qref
  nAssignments <- V.size dvec
  case decisionIndex >= nAssignments of
    True -> kEmpty
    False -> do
      lit <- V.unsafeReadVector dvec decisionIndex
      P.modifyRef' qref (+1)
      kProp lit
{-# INLINE withQueuedDecision #-}


-- | This function is called on a 'Literal' whose value has been decided.
--
-- The task here is to look up all of the clauses that were watching
-- @¬lit@ and update their watchlists.
--
-- If a clause becomes unit, we have two options:
--
-- * Either we can make an assignment to make it True, or
--
-- * We cannot (due to a conflict)
--
-- In the first case, we make the assignment (which implicitly adds
-- that newly decided literal to the queue).  Otherwise, we invoke the
-- conflict continuation, which will backtrack and drain the queue
-- (since those assignments are being undone, we do not need to
-- propagate their units).
--
-- During this process, we remove elements from the inverse watchlist
-- (the list of clauses watching each literal) as we find new watched
-- variables.  In the case we cannot find a new watch (because the
-- clause is unit), we leave the entry in the inverse watchlist.  This
-- way, the watchlist is consistent after we backtrack.  In the case
-- we don't backtrack the decision, it doesn't matter because the
-- clause is satisfied.
updateWatchlists :: L.Literal -- ^ Literal causing the update
                 -> (Constraint -> Solver a) -- ^ Continuation on a conflicting assignment
                 -> Solver a -- ^ Unsat continuation
                 -> Solver a -- ^ Continuation on successful watchlist update
                 -> Solver a
updateWatchlists l kConflict kUnsat kNext = do
  e <- ask
  P.modifyRef' (ePropagations e) (+1)
  clausesWatching <- GA.unsafeReadArray (eClausesWatchingLiteral e) falseLit
  dl <- C.getDecisionLevel
  sz <- V.size clausesWatching
  go dl clausesWatching (sz - 1)
  where
    falseLit = L.neg l
    go dl watchers ix = do
      case ix >= 0 of
        False -> do
          liftIO $ D.traceIO ("      [uw] Successfully updated all watches")
          -- We have successfully found a new set of consistent
          -- watches
          kNext
        True -> do
          con <- V.unsafeReadVector watchers ix
          liftIO $ D.traceIO ("  [uw] Updating watches for clause at index: " ++ show ix)
          propRes <- CO.constraintPropagate con falseLit
          case propRes of
            PropagationNewWatch -> do
              V.unsafeRemoveElement watchers ix
              go dl watchers (ix - 1)
            PropagationKeepWatch -> go dl watchers (ix - 1)
            PropagationConflict ->
              case () of
                _ | dl <= 0 -> do
                      liftIO $ D.traceIO "    [uw] Deriving unsat in updateWatchlists"
                      kUnsat
                  | otherwise -> do
                      clearPropagationQueue
                      liftIO $ D.traceIO ("    [uw] Encountered a unit conflict due")
                      kConflict con

-- | Clear the propagation queue.
--
-- If we find a conflict while during unit propagation, we switch to
-- conflict analysis.  That code assumes that the propagation queue is
-- empty.
clearPropagationQueue :: Solver ()
clearPropagationQueue = do
  e <- ask
  nAssignments <- V.size (eDecisionStack e)
  P.writeRef (ePropagationQueue e) nAssignments


{- Note [Unit Propagation]

This implementation uses a two watched literal scheme, meaning that it
watches two literals in each clause.  It maintains the invariant that
each clause is either satisfied or watching only unassigned literals.
When a new watch cannot be found for a clause after an update, that
clause becomes *unit*.  The final literal is then assigned to be
satisfied, maintaining the invariant.

Right before a new decision is made, the watchlist is always
consistent.

-}
