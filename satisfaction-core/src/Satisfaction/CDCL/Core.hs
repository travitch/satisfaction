module Satisfaction.CDCL.Core (
  assertLiteral,
  learnClause,
  undoUntil,
  withNextDecidedLiteral,
  getDecisionLevel,
  incrementDecisionLevel,
  literalValue,
  bumpVariableActivity,
  decayVariableActivity,
  bumpClauseActivity,
  decayClauseActivity,
  restartWith,
  extractAssignment
  ) where

import Control.Monad ( replicateM_ )
import Data.IORef
import Prelude

import qualified Data.Array.Heap as H
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed as PUA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

import qualified Satisfaction.CDCL.Clause as C
import qualified Satisfaction.Formula.Literal as L
import qualified Satisfaction.Internal.Debug as D
import Satisfaction.CDCL.Monad

-- | The maximum activity value allowed before all activities are
-- normalized.
activityCap :: Double
activityCap = 1e100

-- | If we have passed the conflict threshold, restart by calling
-- @kRestart@.  Otherwise, continue searching.
--
-- If the number of restarts overflows an Int, just set it to -1.
restartWith :: Solver a -> Solver a -> Solver a
restartWith kRestart kSearch = do
  e <- ask
  curConflicts <- P.readRef (eCurrentConflicts e)
  maxConflicts <- P.readRef (eMaxConflicts e)
  case curConflicts < maxConflicts || maxConflicts == -1 of
    True -> kSearch
    False -> do
      let conf = eConfig e
          nextGrowth = fromIntegral maxConflicts * cMaxConflictGrowthFactor conf
      P.modifyRef' (eTotalConflicts e) (+curConflicts)
      P.writeRef (eCurrentConflicts e) 0
      P.writeRef (eMaxConflicts e) (max (floor nextGrowth) (-1))
      P.modifyRef' (eRestartCount e) (+1)
      maxLearned <- P.readRef (eMaxLearnedClauses e)
      let nextMaxLearned = fromIntegral maxLearned * cMaxLearnedClauseGrowthFactor conf
      P.writeRef (eMaxLearnedClauses e) (floor nextMaxLearned)
      undoUntil 0
      kRestart

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
  dl <- getDecisionLevel
  liftIO $ D.traceIO ("[lc] Learning clause and asserting " ++ show assertedLit ++ " at dl " ++ show dl)
  case otherLits of
    [] -> assertLiteral assertedLit Nothing
    _ -> do
      P.modifyRef' (eLearnedClauseCount e) (+1)
      cl <- allocateLearnedClause (assertedLit : otherLits)
      liftIO $ D.traceIO ("  [lc] Clause ref allocated")
      V.push (eLearnedClauses e) cl
      lw1 <- GA.unsafeReadArray (eClausesWatchingLiteral e) assertedLit
      V.push lw1 cl
      -- Set the second watched literal to the first one that was set
      -- at @btLevel@.
      watchFirstAtLevel btLevel cl
      assertLiteral assertedLit (Just cl)

watchFirstAtLevel :: Int -> C.Clause Solver -> Solver ()
watchFirstAtLevel btLevel cl = do
  nLits <- C.literalCount cl
  go 1 nLits cl
  where
    go ix nLits c
      | ix >= nLits = error ("impossible: No matching literal/level for watchFirstAtLevel: " ++ show btLevel)
      | otherwise = do
          e <- ask
          lit <- C.unsafeReadLiteral cl ix
          lvl <- GA.unsafeReadArray (eVarLevels e) (L.var lit)
          case lvl == btLevel of
            False -> go (ix + 1) nLits cl
            True -> do
              lw <- GA.unsafeReadArray (eClausesWatchingLiteral e) lit
              V.push lw c
              C.unsafeSwapLiterals c 1 ix

-- | Return an unused 'ClauseRef', allocating space for a new one if
-- necessary.  If space must be allocated, this function also extends
-- 'eWatchedLiterals' so that there is sufficient space in the
-- watchlist.
allocateLearnedClause :: [L.Literal] -> Solver (C.Clause Solver)
allocateLearnedClause lits = do
  case () of
    _ | length lits <= 1 -> error ("Invalid learned clause: " ++ show lits)
      | otherwise -> return ()
  c <- C.new 0 lits
  C.setLearnedFlag c
  return c
{-# INLINE allocateLearnedClause #-}

-- | Determine the value of the given 'L.Literal'
--
-- This looks at the assignment of the underlying 'L.Variable' and
-- corrects it for the polarity of the literal.
literalValue :: L.Literal -> Solver L.Value
literalValue l = do
  assignments <- asks eAssignment
  val <- GA.unsafeReadArray assignments (L.var l)
  return $! L.litValue l val
{-# INLINE literalValue #-}

-- | Undo the most recent decision, along with the associated metadata.
undoLastDecision :: Solver ()
undoLastDecision =
  withLastDecision $ \lastLit -> do
    liftIO $ D.traceIO ("  Undoing " ++ show lastLit)
    decisions <- asks eDecisionStack
    assignVariableValue (L.var lastLit) L.unassigned Nothing
    resetVariable (L.var lastLit)
    e <- ask
    H.insert (eVariableOrder e) (L.var lastLit)
    V.pop decisions 1
{-# INLINE undoLastDecision #-}

-- | Undo assignments until the given decision level.  This is for use
-- in non-chronological backjumping.
undoUntil :: Int -> Solver ()
undoUntil targetDl = do
  dl <- getDecisionLevel
  case dl > targetDl of
    False -> return ()
    True -> do
      e <- ask
      nAssignments <- V.size (eDecisionStack e)
      dlBoundary <- V.unsafeReadVector (eDecisionBoundaries e) targetDl
      replicateM_ (nAssignments - dlBoundary) undoLastDecision
      P.writeRef (ePropagationQueue e) dlBoundary
      nBounds <- V.size (eDecisionBoundaries e)
      V.pop (eDecisionBoundaries e) (nBounds - targetDl)

-- | Looks up the last decision made and calls the given continuation with it.
--
-- The function doesn't do anything else, so undoing the last decision
-- is safe.
withLastDecision :: (L.Literal -> Solver a) -> Solver a
withLastDecision k = do
  e <- ask
  nDecisions <- V.size (eDecisionStack e)
  lastLit <- V.unsafeReadVector (eDecisionStack e) (nDecisions - 1)
  k lastLit
{-# INLINE withLastDecision #-}

-- | Find the next 'Variable' to assign a value to, implicitly
-- encoding that as a 'Literal'.
--
-- If there are no more variables to assign, extract a solution with
-- the given continuation.
withNextDecidedLiteral :: Solver a -- ^ Continue into the done state (i.e., extract a solution)
                       -> (L.Literal -> Solver a) -- ^ Continue with selected 'Literal'
                       -> Solver a
withNextDecidedLiteral kDone kLit = go
  where
    go = do
      e <- ask
      mvar <- H.takeMin (eVariableOrder e)
      case mvar of
        Nothing -> kDone
        Just var -> do
          val <- GA.unsafeReadArray (eAssignment e) var
          case L.isUnassigned val of
            True -> do
              P.modifyRef' (eDecisionCount e) (+1)
              kLit (L.toPositiveLiteral var)
            False -> go
{-# INLINE withNextDecidedLiteral #-}


-- | Assert a literal.
--
-- This function assumes (but does not check) that the assertion does
-- not cause a conflict.  If it could, call 'tryAssertLiteral'
-- instead.
assertLiteral :: L.Literal -> Maybe (C.Clause Solver) -> Solver ()
assertLiteral lit reason = do
  e <- ask
  let var = L.var lit
      val = L.satisfyLiteral lit
  assignVariableValue var val reason
  V.unsafePush (eDecisionStack e) lit
{-# INLINE assertLiteral #-}


-- | Increment the current decision level
--
-- The decision level is implicit, and represented as the length of
-- the 'eDecisionBoundaries' list.  This function saves the current
-- size of the decision stack as the new boundary, which increments
-- the decision level.
incrementDecisionLevel :: Solver ()
incrementDecisionLevel = do
  e <- ask
  dl <- V.size (eDecisionStack e)
  V.unsafePush (eDecisionBoundaries e) dl
  level <- getDecisionLevel
  liftIO $ D.traceIO ("[idl] At decision level " ++ show level ++ ", which starts at index " ++ show dl)

resetVariable :: L.Variable -> Solver ()
resetVariable var = do
  e <- ask
  liftIO $ D.traceIO ("[reset] Setting the state of " ++ show var ++ " to triedNothing")
  GA.unsafeWriteArray (eAssignment e) var L.unassigned
  GA.unsafeWriteArray (eVarLevels e) var (-1)
  GA.unsafeWriteArray (eDecisionReasons e) var Nothing
{-# INLINE resetVariable #-}

-- | Extract the current assignment as a pure value.
--
-- This does not ensure that the assignment is complete (i.e., there
-- could be unassigned values).
extractAssignment :: Solver (PUA.Array L.Variable L.Value)
extractAssignment = do
  a <- asks eAssignment
  PUMA.freeze a


-- | Implicitly decay variable activities by *increasing* the variable
-- activity increment.
decayVariableActivity :: Solver ()
decayVariableActivity = do
  e <- ask
  let decayFactor = cVariableActivityDecayFactor (eConfig e)
  liftIO $ modifyIORef' (eVariableIncrement e) (* (1 / decayFactor))

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
  case act1 > activityCap of
    False -> return ()
    True -> do
      let arr = eVariableActivity e
          factor = 1 / activityCap
      AT.forMArray_ arr $ \ix elt -> do
        GA.unsafeWriteArray arr ix (elt * factor)
      P.modifyRef' (eVariableIncrement e) (* factor)
  H.unsafeUpdate (eVariableOrder e) var

-- | Decay existing clause activities implicitly by *increasing* the
-- clause increment value
decayClauseActivity :: Solver ()
decayClauseActivity = do
  e <- ask
  let decayFactor = cClauseActivityDecayFactor (eConfig e)
  liftIO $ modifyIORef' (eClauseIncrement e) (* (1 / decayFactor))

-- | Bump the activity of a learned clause.
--
-- Calling this function on a problem (i.e., non-learned) clause is
-- safe and is a no-op
bumpClauseActivity :: C.Clause Solver -> Solver ()
bumpClauseActivity cl = do
  e <- ask
  isLearned <- C.readIsLearned cl
  case isLearned of
    False -> return ()
    True -> do
      amount <- P.readRef (eClauseIncrement e)
      act0 <- C.readActivity cl
      let act1 = act0 + amount
      C.writeActivity cl act1
      case act1 > activityCap of
        False -> return ()
        True -> do
          let arr = eLearnedClauses e
              factor = 1 / activityCap
          AT.forMArray_ arr $ \_ix lc -> do
            a <- C.readActivity lc
            C.writeActivity lc (a * factor)
          P.modifyRef' (eClauseIncrement e) (* factor)
