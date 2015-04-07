{-# LANGUAGE FlexibleContexts #-}
-- | Functions for unit propagation using two-watched literals
module Satisfaction.Internal.UnitPropagation (
  withQueuedDecision,
  updateWatchlists
  ) where

import qualified Data.Array.Prim.Generic as GA
import Data.Bits ( shiftL )
import qualified Data.Ref.Prim as P

import qualified Data.Array.Vector as V
import qualified Satisfaction.CNF as C
import qualified Satisfaction.Internal.Literal as L
import qualified Satisfaction.Internal.Debug as D
import Satisfaction.Internal.Monad

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
                 -> (ClauseRef -> Solver a) -- ^ Continuation on a conflicting assignment
                 -> Solver a -- ^ Unsat continuation
                 -> Solver a -- ^ Continuation on successful watchlist update
                 -> Solver a
updateWatchlists l kConflict kUnsat kNext = do
  e <- ask
  P.modifyRef' (ePropagations e) (+1)
  clausesWatching <- GA.unsafeReadArray (eClausesWatchingLiteral e) falseLit
  go clausesWatching 0
  where
    falseLit = L.neg l
    -- This is invoked if we can't find another literal to watch.
    -- This means that the clause is unit and we can try to satisfy it
    -- by satisfying the remaining variable.
    kUnit clauseNum otherLit watchers ix = do
      liftIO $ D.traceIO ("      [uw] Clause is unit: " ++ show clauseNum)
      val <- literalValue otherLit
      -- If the other literal is unassigned, we can assign it (and
      -- implicitly enqueue it to propagate units).  It cannot be
      -- True, because we handle that in a case of 'go' (see the
      -- otherVal == liftedTrue check)
      --
      -- Otherwise, we have a conflict.  Clean up and then backtrack.
      -- We can get a conflict (despite watchlist tracking) if we made
      -- an assignment that cause a conflict, but the conflicting
      -- update is in the queue and not processed yet.
      dl <- getDecisionLevel
      case () of
        _ | L.isUnassigned val -> do
              liftIO $ D.traceIO ("    [uw] Asserting a literal during watchlist update: " ++ show otherLit)
              assertLiteral otherLit clauseNum
              go watchers (ix + 1)
          | dl <= 0 -> do
              liftIO $ D.traceIO ("    [uw] Deriving unsat in updateWatchlists")
              kUnsat
          | otherwise -> do
              clearPropagationQueue
              liftIO $ D.traceIO ("    [uw] Encountered a unit conflict due to " ++ show otherLit ++ ", which is assigned " ++ show val)
              kConflict clauseNum
    go watchers ix = do
      sz <- V.size watchers
      case ix < sz of
        False -> do
          liftIO $ D.traceIO ("      [uw] Successfully updated all watches")
          -- We have successfully found a new set of consistent
          -- watches
          kNext
        True -> do
          clauseNum <- V.unsafeReadVector watchers ix
          cl <- clauseAt clauseNum
          liftIO $ D.traceIO ("  [uw] Updating watches for clause " ++ show clauseNum ++ ": " ++ show cl)
          e <- ask
          otherLit <- normalizeWatchedLiterals clauseNum falseLit
          -- falseLit is @¬l@ and known to be false.  It is at the
          -- given index.  We have to check to see if the other lit
          -- is true; if so, this clause is satisfied and we don't
          -- need to update anything.
          otherVal <- literalValue otherLit
          case otherVal == L.liftedTrue of
            True -> do
              -- The clause is satisfied, so we don't need to change our watches at all.
              liftIO $ D.traceIO "      [uw] Satisfied clause"
              go watchers (ix + 1)
            False -> do
              -- Find a new lit to watch instead of falseLit.  If
              -- this succeeds, we need to remove the clause at @ix@
              -- (which is @clauseNum@) and add @clauseNum@ to the appropriate list
              let whenUnit = kUnit clauseNum otherLit watchers ix
              withTrueOrUnassignedLiteral whenUnit cl otherLit $ \newWatchedLit -> do
                liftIO $ D.traceIO ("    [uw] Now watching " ++ show newWatchedLit)
                GA.unsafeWriteArray (eWatchedLiterals e) (2 * clauseNum + 1) newWatchedLit
                V.removeElement watchers ix
                watchingLit <- GA.unsafeReadArray (eClausesWatchingLiteral e) newWatchedLit
                V.push watchingLit clauseNum
                -- We don't increment @ix@ because we removed the
                -- element that was at @ix@ and replaced it with a
                -- new one, so we need to check ix again.
                go watchers ix
{-# INLINE updateWatchlists #-}

-- | Place the literal we are updating (the one known to be false due
-- to unit propagation) into the second watched literal slot.  We'll
-- implicitly know to update this one in 'updateWatchlists'.
--
-- The other literal is in the first watched literal slot, and is
-- returned here.  In 'updateWatchlists', we can return if that
-- literal is already True.
normalizeWatchedLiterals :: ClauseRef -> L.Literal -> Solver L.Literal
normalizeWatchedLiterals clauseRef falseLit = do
  e <- ask
  let watches = eWatchedLiterals e
  watch1 <- GA.unsafeReadArray watches watch1Ix
  watch2 <- GA.unsafeReadArray watches watch2Ix
  case watch2 == falseLit of
    True -> return watch1
    False -> do
      GA.unsafeWriteArray watches watch1Ix watch2
      GA.unsafeWriteArray watches watch2Ix watch1
      return watch2
  where
    watch1Ix = clauseRef `shiftL` 1
    watch2Ix = watch1Ix + 1
{-# INLINE normalizeWatchedLiterals #-}

-- | Find a new literal that is either satisfied or unassigned in the given clause.
--
-- If there is no such literal, call the conflict continuation.
withTrueOrUnassignedLiteral :: Solver a -- ^ Continuation for the case we can't find a new literal to watch
                            -> C.Clause -- ^ The clause to search
                            -> L.Literal -- ^ The literal we don't want to choose (because we are already watching it)
                            -> (L.Literal -> Solver a) -- ^ The continuation to call with the new literal
                            -> Solver a
withTrueOrUnassignedLiteral kConflict clause ignoreLit withLit = go 0
  where
    sz = C.clauseSize clause
    go ix | ix >= sz = kConflict
          | otherwise = do
              let l = clause `C.clauseLiteral` ix
              case l == ignoreLit of
                True -> go (ix + 1)
                False -> do
                  lv <- literalValue l
                  case lv == L.liftedFalse of
                    False -> withLit l
                    True -> go (ix + 1)
{-# INLINE withTrueOrUnassignedLiteral #-}

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
