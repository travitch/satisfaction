{-# LANGUAGE BangPatterns #-}
-- | Conflict analysis based on the first UIP heuristic
--
-- See Note [First UIP] for details.
module Satisfaction.CDCL.AnalyzeConflict (
  Conflict(..),
  analyzeConflict
  ) where

import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

import qualified Satisfaction.CDCL.Clause as CL
import qualified Satisfaction.CDCL.Core as C
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
analyzeConflict :: (Conflict -> Solver a) -> CL.Clause Solver -> Solver a
analyzeConflict k conflictClause = do
  e <- ask
  P.modifyRef' (eCurrentConflicts e) (+1)
  nAssignments <- V.size (eDecisionStack e)
  clearSeenMarkers
  C.bumpClauseActivity conflictClause
  withFalseLiterals conflictClause 0 0 [] $ \nodesToUIP maxLevel learnt -> do
    withNextConflictLit (nAssignments - 1) $ \p confl assignmentIndex -> do
--      liftIO $ D.traceIO ("  [ac] Entering conflict analysis loop with clause at " ++ show conflIndex)
      go p confl assignmentIndex (nodesToUIP - 1) maxLevel learnt
  where
    -- The conflict analysis loop.
    --
    -- See Note [Conflict Analysis State]
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
          C.bumpClauseActivity confl
          liftIO $ D.traceIO ("  [ac] Expanding reason for " ++ show p ++ " in conflict clause")
          withFalseLiterals confl nodesToUIP maxLevel learnt $ \nodesToUIP' maxLevel' learnt' -> do
            withNextConflictLit assignmentIndex $ \p' confl' assignmentIndex' -> do
              liftIO $ D.traceIO ("  [ac] Inspecting conflict lit " ++ show p)
              liftIO $ D.traceIO ("  [ac] Kicking off another loop iteration with counter " ++ show (nodesToUIP' - 1))
              go p' confl' assignmentIndex' (nodesToUIP' - 1) maxLevel' learnt'
      | otherwise = error "Got an unexpected empty conflict clause while searching for a UIP"

withFalseLiterals :: CL.Clause Solver -- ^ The conflict clause
                  -> Int -- ^ The UIP counter
                  -> Int -- ^ The decision level to backtrack to
                  -> [L.Literal] -- ^ Literals comprising the learned clause
                  -> (Int -> Int -> [L.Literal] -> Solver a) -- ^ Continuation with updated values of the counter, dl, and learned literals
                  -> Solver a
withFalseLiterals conflictClause nodesToUIP0 maxLevel0 learnt0 kDone = do
  nLits <- CL.literalCount conflictClause
  go (nLits - 1) nodesToUIP0 maxLevel0 learnt0
  where
    go !ix nodesToUIP maxLevel learnt
      | ix < 0 = kDone nodesToUIP maxLevel learnt
      | otherwise = do
          lit <- CL.unsafeReadLiteral conflictClause ix
          val <- C.literalValue lit
          case val == L.liftedFalse of
            False -> go (ix - 1) nodesToUIP maxLevel learnt
            True -> processReason lit (ix - 1) nodesToUIP maxLevel learnt
    processReason lit !ix nodesToUIP maxLevel learnt = do
      let var = L.var lit
      e <- ask
      wasSeen <- GA.unsafeReadArray (eSeen e) var
      varAssignedAtLevel <- GA.unsafeReadArray (eVarLevels e) var
      case wasSeen /= 1 && varAssignedAtLevel > 0 of
        False -> go ix nodesToUIP maxLevel learnt
        True -> do
          dl <- getDecisionLevel
          -- If the variable was assigned at the current decision
          -- level, we want to expand the clause that caused that to
          -- happen into our reason.  To do that, we just increment
          -- reasonsAtDl to extend our search backwards.
          --
          -- Otherwise, it was assigned at a lower level and we want
          -- it to be part of our learned clause (ignoring dl == 0)
          GA.unsafeWriteArray (eSeen e) var 1
          C.bumpVariableActivity var
          case varAssignedAtLevel of
            _ | varAssignedAtLevel >= dl -> do
                  liftIO $ D.traceIO (" [wfl] Skipping lit " ++ show lit ++ " because it was assigned at dl " ++ show varAssignedAtLevel)
                  go ix (nodesToUIP + 1) maxLevel learnt
              | otherwise -> do
                  liftIO $ D.traceIO (" [wfl] lit " ++ show lit ++ " assigned at " ++ show varAssignedAtLevel ++ " in clause ") --  ++ show conflictClause)
                  let maxLevel' = max maxLevel varAssignedAtLevel
                      learnt' = lit : learnt
                  go ix nodesToUIP maxLevel' learnt'
{-# INLINE withFalseLiterals #-}

-- Pull the next relevant literal (along with the clause that
-- implied it) from the assignment stack, undoing the assignment
-- before continuing.
--
-- It cannot be the case that there are no decisions here, hence
-- the unsafe read.
withNextConflictLit :: Int -> (L.Literal -> Maybe (CL.Clause Solver) -> Int -> Solver a) -> Solver a
withNextConflictLit lastLitIndex kLit = go lastLitIndex
  where
    go ix = do
      e <- ask
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


{- Note [First UIP]

-}
