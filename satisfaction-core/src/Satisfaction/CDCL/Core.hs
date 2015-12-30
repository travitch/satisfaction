{-# LANGUAGE FlexibleContexts #-}
module Satisfaction.CDCL.Core (
  -- * Decisions
  withNextDecidedLiteral,
  getDecisionLevel,
  incrementDecisionLevel,
  -- * Values
  assertLiteral,
  tryAssertLiteral,
  literalValue,
  variableValue,
  watchLiteral,
  unwatchLiteral,
  extractAssignment,
  assignVariableValue,
  -- * Restarts
  undoUntil,
  restartWith,
  -- * Activity
  decayVariableActivity,
  decayClauseActivity,
  rescaleActivity,
  activityCap
  ) where

import Control.Monad ( replicateM_ )
import Prelude

import qualified Data.Array.Heap as H
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed as PUA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

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

-- | Determine the current value of the given 'L.Variable'.
variableValue :: L.Variable -> Solver L.Value
variableValue v = do
  assignments <- asks eAssignment
  GA.unsafeReadArray assignments v
{-# INLINE variableValue #-}

-- | Undo the most recent decision, along with the associated metadata.
undoLastDecision :: Solver ()
undoLastDecision = do
  e <- ask
  nDecisions <- V.size (eDecisionStack e)
  lastLit <- V.unsafeReadVector (eDecisionStack e) (nDecisions - 1)
  liftIO $ D.traceIO ("  Undoing " ++ show lastLit)
  assignVariableValue (L.var lastLit) L.unassigned Nothing
  resetVariable (L.var lastLit)
  H.insert (eVariableOrder e) (L.var lastLit)
  V.pop (eDecisionStack e) 1
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


-- | Get the current decision level
getDecisionLevel :: Solver Int
getDecisionLevel = do
  bv <- asks eDecisionBoundaries
  V.size bv
{-# INLINE getDecisionLevel #-}

-- | Assign a 'L.Value' to a 'L.Variable'.
--
-- Note that the 'State' is always required to be updated at the same
-- time.
assignVariableValue :: L.Variable -> L.Value -> Maybe Constraint -> Solver ()
assignVariableValue var val reason = do
  e <- ask
  dl <- getDecisionLevel
  liftIO $ D.traceIO ("  [assign] Assigning " ++ show val ++ " to " ++ show var ++ " at " ++ show dl)
  GA.unsafeWriteArray (eAssignment e) var val
  GA.unsafeWriteArray (eVarLevels e) var dl
  GA.unsafeWriteArray (eDecisionReasons e) var reason
{-# INLINE assignVariableValue #-}

-- | Assert a literal.
--
-- This function assumes (but does not check) that the assertion does
-- not cause a conflict.  If it could, call 'tryAssertLiteral'
-- instead.
assertLiteral :: L.Literal -> Maybe Constraint -> Solver ()
assertLiteral lit reason = do
  e <- ask
  let var = L.var lit
      val = L.satisfyLiteral lit
  assignVariableValue var val reason
  V.push (eDecisionStack e) lit
{-# INLINE assertLiteral #-}

-- | Try to assert a literal, returning False if the assertion causes
-- a contradiction.
--
-- If the attempted assertion matches one already in the solver state,
-- we keep the original reason for the assertion (instead of
-- overwriting it).
tryAssertLiteral :: L.Literal -> Maybe Constraint -> Solver Bool
tryAssertLiteral lit reason = do
  e <- ask
  let var = L.var lit
      val = L.satisfyLiteral lit
  val0 <- GA.unsafeReadArray (eAssignment e) var
  case val0 /= L.unassigned of
    True | val0 == val -> return True
         | otherwise -> return False
    False -> do
      assignVariableValue var val reason
      V.push (eDecisionStack e) lit
      return True

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
  V.push (eDecisionBoundaries e) dl
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
  P.modifyRef' (eVariableIncrement e) (* (1 / decayFactor))

-- | Decay existing clause activities implicitly by *increasing* the
-- clause increment value
decayClauseActivity :: Solver ()
decayClauseActivity = do
  e <- ask
  let decayFactor = cClauseActivityDecayFactor (eConfig e)
  P.modifyRef' (eClauseIncrement e) (* (1 / decayFactor))

-- | Rescale the activity of all constraints
rescaleActivity :: Solver ()
rescaleActivity = do
  e <- ask
  let arr = eLearnedClauses e
      factor = 1 / activityCap
  AT.forMArray_ arr $ \_ix lc -> do
    case lc of
      Constraint CI { conReadActivity = readAct, conWriteActivity = writeAct } v -> do
        a <- readAct lc v
        writeAct lc v (a * factor)
  P.modifyRef' (eClauseIncrement e) (* factor)

watchLiteral :: Constraint -> L.Literal -> Solver ()
watchLiteral con l = do
  wls <- asks eClausesWatchingLiteral
  v <- GA.unsafeReadArray wls l
  V.push v con

unwatchLiteral :: Constraint -> L.Literal -> Solver ()
unwatchLiteral con0 l = do
  wls <- asks eClausesWatchingLiteral
  v <- GA.unsafeReadArray wls l
  nClauses <- V.size v
  go con0 v (nClauses - 1)
  where
    go con v ix
      | ix < 0 = error ("Could not find literal " ++ show l ++ " in watchlist")
      | otherwise = do
          cl <- V.unsafeReadVector v ix
          case cl == con of
            False -> go con v (ix - 1)
            True -> do
              V.unsafeWriteVector v ix sentinelClause
              V.removeElement v ix

sentinelClause :: Constraint
sentinelClause = error "Simplifier sentinel constraint"
