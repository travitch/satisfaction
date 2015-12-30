{-# LANGUAGE BangPatterns #-}
-- | Conflict analysis based on the first UIP heuristic
--
-- See Note [First UIP] for details.
module Satisfaction.CDCL.AnalyzeConflict (
  Conflict(..),
  analyzeConflict
  ) where

import qualified Control.Exception as E

import qualified Data.Array.Heap as H
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

import qualified Satisfaction.CDCL.Core as C
import qualified Satisfaction.CDCL.Constraint as CO
import Satisfaction.CDCL.Monad
import qualified Satisfaction.Formula.Literal as L
import qualified Satisfaction.Internal.Debug as D

-- | A description of a conflict that tells us what conflict clause we
-- should learn.
data Conflict = Conflict { cAssertingLit :: !L.Literal
                         , cOtherLits :: [L.Literal]
                         , cBacktrackLevel :: !Int
                         }

-- | Analyze the conflict that caused the given clause to become unsatisfied.
--
-- Calls the given continuation with the literal to assert, the clause
-- to learn, and the decision level to backtrack to.
analyzeConflict :: (Conflict -> Solver a) -> Constraint -> Solver a
analyzeConflict k conflict0 = do
  e <- ask
  P.modifyRef' (eCurrentConflicts e) (+1)
  nAssignments <- V.size (eDecisionStack e)
  clearSeenMarkers
  withAccumulatingReason conflict0 0 0 Nothing [] $ \nodesToUIP maxLevel currentReason -> do
    withNextConflictLit (nAssignments - 1) $ \p confl assignmentIndex -> do
      go p confl assignmentIndex (nodesToUIP - 1) maxLevel currentReason
  where
    go p mConfl assignmentIndex nodesToUIP maxLevel learnt
      | nodesToUIP <= 0 = do
          let p' = L.neg p
          case learnt of
            [] -> do
              liftIO $ D.traceIO ("  [ac] Calling conflict continuation with unit clause " ++ show [p'])
              k Conflict { cAssertingLit = p'
                         , cOtherLits = []
                         , cBacktrackLevel = 0
                         }
            _ -> do
              liftIO $ D.traceIO ("  [ac] Calling the conflict continuation with " ++ show (p':learnt) ++ " and max level " ++ show maxLevel)
              k Conflict { cAssertingLit = p'
                         , cOtherLits = learnt
                         , cBacktrackLevel = maxLevel
                         }
      | Just confl <- mConfl = do
          withAccumulatingReason confl nodesToUIP maxLevel (Just p) learnt $ \nodesToUIP' maxLevel' learnt' -> do
            withNextConflictLit assignmentIndex $ \p' confl' assignmentIndex' -> do
              liftIO $ D.traceIO ("  [ac] Inspecting conflict lit " ++ show p)
              liftIO $ D.traceIO ("  [ac] Kicking off another loop iteration with counter " ++ show (nodesToUIP' - 1))
              go p' confl' assignmentIndex' (nodesToUIP' - 1) maxLevel' learnt'
      | otherwise = error "Got an unexpected empty conflict clause while searching for a UIP"

withAccumulatingReason :: Constraint
                       -> Int -- ^ The UIP counter
                       -> Int -- ^ The decision level to backtrack to
                       -> Maybe L.Literal -- ^ p
                       -> [L.Literal] -- ^ Literals comprising the learned clause
                       -> (Int -> Int -> [L.Literal] -> Solver a) -- ^ Continuation with updated values of the counter, dl, and learned literals
                       -> Solver a
withAccumulatingReason conflict nodesToUIP0 maxLevel0 p0 learnt0 kDone = do
  -- Note that this call to calculateConflictReason manipulates the
  -- constraint activity, if any.
  reasonLits <- CO.constraintCalculateConflictReason conflict p0
  go reasonLits nodesToUIP0 maxLevel0 learnt0
  where
    go reasonLits nodesToUIP maxLevel learnt =
      case reasonLits of
        [] -> kDone nodesToUIP maxLevel learnt
        lit : rest -> do
          val <- C.literalValue lit
          -- Note, this check is probably unnecessary now that we have
          -- 'calculateConflictReason', which won't return the True lit
          case val == L.liftedFalse of
            False -> go rest nodesToUIP maxLevel learnt
            True -> processReason lit rest nodesToUIP maxLevel learnt
    processReason lit rest nodesToUIP maxLevel learnt = do
      let var = L.var lit
      e <- ask
      wasSeen <- GA.unsafeReadArray (eSeen e) var
      varAssignedAtLevel <- GA.unsafeReadArray (eVarLevels e) var
      case wasSeen /= 1 && varAssignedAtLevel > 0 of
        False -> go rest nodesToUIP maxLevel learnt
        True -> do
          dl <- C.getDecisionLevel
          -- If the variable was assigned at the current decision
          -- level, we want to expand the clause that caused that to
          -- happen into our reason.  To do that, we just increment
          -- reasonsAtDl to extend our search backwards.
          --
          -- Otherwise, it was assigned at a lower level and we want
          -- it to be part of our learned clause (ignoring dl == 0)
          GA.unsafeWriteArray (eSeen e) var 1
          bumpVariableActivity var
          case varAssignedAtLevel of
            _ | varAssignedAtLevel >= dl -> do
                  liftIO $ D.traceIO (" [wfl] Skipping lit " ++ show lit ++ " because it was assigned at dl " ++ show varAssignedAtLevel)
                  go rest (nodesToUIP + 1) maxLevel learnt
              | otherwise -> do
                  liftIO $ D.traceIO (" [wfl] lit " ++ show lit ++ " assigned at " ++ show varAssignedAtLevel ++ " in clause")
                  let maxLevel' = max maxLevel varAssignedAtLevel
                      learnt' = lit : learnt
                  go rest nodesToUIP maxLevel' learnt'

-- Pull the next relevant literal (along with the clause that
-- implied it) from the assignment stack, undoing the assignment
-- before continuing.
--
-- It cannot be the case that there are no decisions here, hence
-- the unsafe read.
withNextConflictLit :: Int -> (L.Literal -> Maybe Constraint -> Int -> Solver a) -> Solver a
withNextConflictLit lastLitIndex kLit = go lastLitIndex
  where
    go ix = do
      -- If this assertion fails, the search for a UIP failed.  See Note [UIP Search]
      E.assert (ix >= 0) (return ())
      e <- ask
      -- Note: This unsafe read in a loop looks funny.  If the UIP
      -- search is correct (which relies on the implementations of
      -- 'calculateReason' being correct), the search will terminate.
      lastLit <- V.unsafeReadVector (eDecisionStack e) ix
      liftIO $ D.traceIO ("    [WNCL] With last decision: " ++ show lastLit)
      seen <- GA.unsafeReadArray (eSeen e) (L.var lastLit)
      case seen == 1 of
        False -> do
          liftIO $ D.traceIO ("      [WNCL] Skipping (unmarked) " ++ show lastLit)
          go (ix - 1)
        True -> do
          -- Note that the returned conflict clause here might be
          -- Nothing.  This means that the search in 'analyzeConflict'
          -- is done and we will end up taking the @nodesToUIP <= 0@
          -- branch.
          mConflict <- GA.unsafeReadArray (eDecisionReasons e) (L.var lastLit)
          reasonLevel <- GA.unsafeReadArray (eVarLevels e) (L.var lastLit)
          liftIO $ D.traceIO ("    [WNCL] Last lit was assigned at dl " ++ show reasonLevel)
--          liftIO $ D.traceIO ("    [WNCL] Conflict index is " ++ show conflictIndex)
          liftIO $ D.traceIO ("      [WNCL] Calling kLit")
          kLit lastLit mConflict (ix - 1)
{-# INLINE withNextConflictLit #-}

-- The seen array is a bitvector marking which literals we have
-- already seen while analyzing the conflict.  It is stored as a
-- part of the solver state so that we don't need to continually
-- re-allocate it.  That means we need to reset its value before
-- we use it each time.
clearSeenMarkers :: Solver ()
clearSeenMarkers = do
  seen <- asks eSeen
  AT.forMArray_ seen $ \ix _ -> do
    GA.unsafeWriteArray seen ix 0

-- | Bump the activity for a 'L.Variable' by the current increment
-- amount.
--
-- This function normalizes all of the activities if they get too
-- large.  See Note [VSIDS]
bumpVariableActivity :: L.Variable -> Solver ()
bumpVariableActivity var = do
  e <- ask
  amount <- P.readRef (eVariableIncrement e)
  act0 <- GA.unsafeReadArray (eVariableActivity e) var
  let act1 = act0 + amount
  GA.unsafeWriteArray (eVariableActivity e) var act1
  case act1 > C.activityCap of
    False -> return ()
    True -> do
      let arr = eVariableActivity e
          factor = 1 / C.activityCap
      AT.forMArray_ arr $ \ix elt -> do
        GA.unsafeWriteArray arr ix (elt * factor)
      P.modifyRef' (eVariableIncrement e) (* factor)
  H.unsafeUpdate (eVariableOrder e) var

{- Note [VSIDS]

VSIDS stands for Variable State Independent Decaying Sum.  It is a
heuristic for choosing the variable assignment order during the
search.  The idea is to assign each variable an activity score.
Activity is increased when a variable is involved in a conflict;
variables involved in more conflicts will be resolved sooner.
Ideally, this resolves conflicts earlier in the search.

-}

{- Note [Conflict Analysis State]

The main conflict analysis loop maintains a few pieces of state:

[assignmentIndex] The pointer into the decision stack (from the top of
the stack) that marks how far we have progressed with the BFS over the
implication graph.  This is the queue for the BFS.

[nodesToUIP] A counter of how many edges of the implication graph we
have seen so far.  Once this counter reaches zero, we have found the
*first* UIP.  Note that this may come before a decision variable in
the best case.  See Note [First UIP] for some details.

[maxLevel] The level to backjump to.  This will be the second highest
decision level in the learned clause (that is, the highest aside from
the single variable present from the *current* decision level).

[learnt] The literals comprising the clause learned from this conflict
(except for the single literal at the current decision level).  That
literal will be added before the continuation is called.

-}

{- Note [UIP Search]

This search for the UIP of the implication graph terminates correctly
if all of the implementations of 'calculateReason' are correct.  If
they are not, the search will index past the beginning of the vector
and segfault.

-}

{- Note [First UIP]

-}
