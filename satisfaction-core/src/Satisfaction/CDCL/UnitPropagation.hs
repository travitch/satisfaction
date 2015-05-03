{-# LANGUAGE FlexibleContexts #-}
-- | Functions for unit propagation using two-watched literals
module Satisfaction.CDCL.UnitPropagation (
  withQueuedDecision,
  updateWatchlists
  ) where

import qualified Data.Array.Prim.Generic as GA
import qualified Data.Ref.Prim as P

import qualified Data.Array.Vector as V
import qualified Satisfaction.CDCL.Clause as CL
import qualified Satisfaction.CDCL.Core as C
import Satisfaction.CDCL.Monad
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
                 -> (CL.Clause Solver -> Solver a) -- ^ Continuation on a conflicting assignment
                 -> Solver a -- ^ Unsat continuation
                 -> Solver a -- ^ Continuation on successful watchlist update
                 -> Solver a
updateWatchlists l kConflict kUnsat kNext = do
  e <- ask
  P.modifyRef' (ePropagations e) (+1)
  clausesWatching <- GA.unsafeReadArray (eClausesWatchingLiteral e) falseLit
  dl <- getDecisionLevel
  go dl clausesWatching 0
  where
    falseLit = L.neg l
    -- This is invoked if we can't find another literal to watch.
    -- This means that the clause is unit and we can try to satisfy it
    -- by satisfying the remaining variable.
    kUnit dl cl otherLit watchers ix = do
      liftIO $ D.traceIO ("      [uw] Clause is unit at index: " ++ show ix)
      val <- C.literalValue otherLit
      -- If the other literal is unassigned, we can assign it (and
      -- implicitly enqueue it to propagate units).  It cannot be
      -- True, because we handle that in a case of 'go' (see the
      -- otherVal == liftedTrue check)
      --
      -- Otherwise, we have a conflict.  Clean up and then backtrack.
      -- We can get a conflict (despite watchlist tracking) if we made
      -- an assignment that cause a conflict, but the conflicting
      -- update is in the queue and not processed yet.
      case () of
        _ | L.isUnassigned val -> do
              liftIO $ D.traceIO ("    [uw] Asserting a literal during watchlist update: " ++ show otherLit)
              C.assertLiteral otherLit (Just cl)
              go dl watchers (ix + 1)
          | dl <= 0 -> do
              liftIO $ D.traceIO ("    [uw] Deriving unsat in updateWatchlists")
              kUnsat
          | otherwise -> do
              clearPropagationQueue
              liftIO $ D.traceIO ("    [uw] Encountered a unit conflict due to " ++ show otherLit ++ ", which is assigned " ++ show val)
              kConflict cl
    go dl watchers ix = do
      sz <- V.size watchers
      case ix < sz of
        False -> do
          liftIO $ D.traceIO ("      [uw] Successfully updated all watches")
          -- We have successfully found a new set of consistent
          -- watches
          kNext
        True -> do
          cl <- V.unsafeReadVector watchers ix
          liftIO $ D.traceIO ("  [uw] Updating watches for clause at index: " ++ show ix)
          otherLit <- normalizeWatchedLiterals cl falseLit
          -- falseLit is @¬l@ and known to be false.  It is at the
          -- given index.  We have to check to see if the other lit
          -- is true; if so, this clause is satisfied and we don't
          -- need to update anything.
          otherVal <- C.literalValue otherLit
          case otherVal == L.liftedTrue of
            True -> do
              -- The clause is satisfied, so we don't need to change our watches at all.
              liftIO $ D.traceIO "      [uw] Satisfied clause"
              go dl watchers (ix + 1)
            False -> do
              -- Find a new lit to watch instead of falseLit.  If
              -- this succeeds, we need to remove the clause at @ix@
              -- (which is @clauseNum@) and add @clauseNum@ to the appropriate list
              let whenUnit = kUnit dl cl otherLit watchers ix
              withTrueOrUnassignedLiteral whenUnit cl $ \newWatchedLitIdx newWatchedLit -> do
                clausesWatchingLiteral <- asks eClausesWatchingLiteral
                liftIO $ D.traceIO ("    [uw] Now watching " ++ show newWatchedLit)
                CL.unsafeSwapLiterals cl 1 newWatchedLitIdx
                V.unsafeRemoveElement watchers ix
                newWatches <- GA.unsafeReadArray clausesWatchingLiteral newWatchedLit
                V.push newWatches cl
                -- We don't increment @ix@ because we removed the
                -- element that was at @ix@ and replaced it with a
                -- new one, so we need to check ix again.
                go dl watchers ix

-- | Re-arrange the watched literals in the clause such that the False
-- literal (i.e., the one that needs to be changed) is first.  Return
-- the other literal.
normalizeWatchedLiterals :: CL.Clause Solver -> L.Literal -> Solver L.Literal
normalizeWatchedLiterals cl falseLit = do
  l0 <- CL.unsafeReadLiteral cl 0
  l1 <- CL.unsafeReadLiteral cl 1
  case l1 == falseLit of
    True -> return l0
    False -> do
      CL.unsafeSwapLiterals cl 0 1
      return l1

-- | Find a new literal that is either satisfied or unassigned in the given clause.
--
-- If there is no such literal, call the conflict continuation.
withTrueOrUnassignedLiteral :: Solver a -- ^ Continuation for the case we can't find a new literal to watch
                            -> CL.Clause Solver -- ^ The clause to search
                            -> (Int -> L.Literal -> Solver a) -- ^ The continuation to call with the new literal
                            -> Solver a
withTrueOrUnassignedLiteral kConflict clause withLit = do
  sz <- CL.literalCount clause
  go 2 sz
  where
    go ix sz
      | ix >= sz = kConflict
      | otherwise = do
          l <- CL.unsafeReadLiteral clause ix
          lv <- C.literalValue l
          case lv == L.liftedFalse of
            False -> withLit ix l
            True -> go (ix + 1) sz

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
