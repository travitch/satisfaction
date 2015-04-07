-- | These are utilities for simplifying the clause database.
--
-- This includes 1) dealing with learning and forgetting learned
-- clauses and 2) simplifying clauses when we backtrack to the ground
-- level.
module Satisfaction.Internal.Simplify (
  reduceLearnedClauses,
  simplifyClauses
  ) where

import qualified Data.Array.Heap as H
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.List as L
import qualified Data.Ref.Prim as P

import qualified Satisfaction.CNF as C
import qualified Satisfaction.Internal.Literal as L
import Satisfaction.Internal.Monad

clauseIsLocked :: ClauseRef -> Solver Bool
clauseIsLocked cref = do
  e <- ask
  wl1 <- GA.unsafeReadArray (eWatchedLiterals e) (cref * 2)
  r1 <- GA.unsafeReadArray (eDecisionReasons e) (L.var wl1)
  return (r1 == cref)
{-# INLINE clauseIsLocked #-}

-- | If we have exceeded our allowed number of learned clauses, throw
-- out about half of them (plus inactive clauses).
--
-- Note: clauses of length two are always kept.
reduceLearnedClauses :: Solver ()
reduceLearnedClauses = do
  e <- ask
  nAssignments <- V.size (eDecisionStack e)
  nLearned <- P.readRef (eLearnedClauseCount e)
  maxLearned <- P.readRef (eMaxLearnedClauses e)
  case maxLearned > nLearned - nAssignments of
    True -> return ()
    False -> removeInactiveClauses nLearned
{-# INLINE reduceLearnedClauses #-}

-- | One approach would be to sort here.  Due to the watchlist
-- representation, sorting would be complicated.  Instead, we use the
-- median-of-medians algorithm to find an approximate median and throw
-- out all of the clauses with less activity than that.
removeInactiveClauses :: Int -> Solver ()
removeInactiveClauses nLearned
  | nLearned == 0 = return ()
  | otherwise = do
      e <- ask
      P.modifyRef' (eLearnedCleanup e) (+1)
      amedian <- approximateMedian nLearned
      clauseInc <- P.readRef (eClauseIncrement e)
      let cutoffActivity = max amedian (clauseInc / fromIntegral nLearned)
      forLearnedClauses () $ \() ix cref cl -> do
        locked <- clauseIsLocked cref
        clAct <- GA.unsafeReadArray (eClauseActivity e) ix
        case locked || clAct > cutoffActivity || C.clauseSize cl == 2 of
          True -> return ()
          False -> removeLearnedClause ix cref
            -- wl1 <- GA.unsafeReadArray (eWatchedLiterals e) (cref * 2)
            -- wl2 <- GA.unsafeReadArray (eWatchedLiterals e) (cref * 2 + 1)
            -- l1Watchers <- GA.unsafeReadArray (eClausesWatchingLiteral e) wl1
            -- l2Watchers <- GA.unsafeReadArray (eClausesWatchingLiteral e) wl2
            -- removeWatchedClause l1Watchers cref
            -- removeWatchedClause l2Watchers cref
            -- H.insert (eClauseRefPool e) ix
            -- modifyIORef' (eLearnedClauseCount e) (subtract 1)

removeLearnedClause :: Int -> ClauseRef -> Solver ()
removeLearnedClause ix cref = do
  e <- ask
  wl1 <- GA.unsafeReadArray (eWatchedLiterals e) (cref * 2)
  wl2 <- GA.unsafeReadArray (eWatchedLiterals e) (cref * 2 + 1)
  l1Watchers <- GA.unsafeReadArray (eClausesWatchingLiteral e) wl1
  l2Watchers <- GA.unsafeReadArray (eClausesWatchingLiteral e) wl2
  removeWatchedClause l1Watchers cref
  removeWatchedClause l2Watchers cref
  H.insert (eClauseRefPool e) ix
  P.modifyRef' (eLearnedClauseCount e) (subtract 1)


forLearnedClauses :: a -> (a -> Int -> ClauseRef -> C.Clause -> Solver a) -> Solver a
forLearnedClauses a k = do
  e <- ask
  nProblemClauses <- GA.size (eProblemClauses e)
  AT.foldMArray (eLearnedClauses e) a $ \ix cl a' -> do
    let cref = ix + nProblemClauses
    refIsAvailable <- H.member (eClauseRefPool e) ix
    case refIsAvailable of
      False -> k a' ix cref cl
      True -> return a'

approximateMedian :: Int -> Solver Double
approximateMedian nLearned = do
  e <- ask
  mstorage <- GA.newArray nLearned 0
  nActivities <- forLearnedClauses 0 $ \counter arrix _cref _cl -> do
    activity <- GA.unsafeReadArray (eClauseActivity e) arrix
    GA.unsafeWriteArray mstorage counter activity
    return (counter + 1)
  medianOfMedians nActivities mstorage

medianOfMedians :: Int
                -> PUMA.MArray Solver Int Double
                -> Solver Double
medianOfMedians nElts arr
  | nElts <= 5 = medianOfFiveFrom 0 arr
  | otherwise = do
      nextN <- go 0 0
      medianOfMedians nextN arr
  where
    go ix nWritten
      | ix >= nElts = return nWritten
      | otherwise = do
          med <- medianOfFiveFrom ix arr
          GA.unsafeWriteArray arr nWritten med
          go (ix + 5) (nWritten + 1)

readFiveFrom :: Int -> PUMA.MArray Solver Int Double -> Solver [Double]
readFiveFrom ix0 arr = do
  sz <- GA.size arr
  go (min (ix0 + 4) (sz - 1)) sz []
  where
    go ix sz acc | ix < ix0 = return acc
                 | otherwise = do
                     elt <- GA.unsafeReadArray arr ix
                     go (ix - 1) sz (elt : acc)
{-# INLINE readFiveFrom #-}

medianOfFiveFrom :: Int -> PUMA.MArray Solver Int Double -> Solver Double
medianOfFiveFrom ix arr = do
  lst <- readFiveFrom ix arr
  case L.sort lst of
    _:_:v3:_:_:_ -> return v3
    _:v2:v3:_:_ -> return (v2 * 0.5 + v3 * 0.5)
    _:v2:_:_ -> return v2
    v1:v2:_ -> return (v1 * 0.5 + v2 * 0.5)
    v1:_ -> return v1
    [] -> error "Empty list in medianOfFiveFrom"

removeWatchedClause :: V.Vector PUMA.MArray Solver ClauseRef -> ClauseRef -> Solver ()
removeWatchedClause watchers cref = do
  len <- V.size watchers
  go 0 len
  where
    go ix len
      | ix >= len = return ()
      | otherwise = do
          elt <- V.unsafeReadVector watchers ix
          case elt == cref of
            False -> go (ix + 1) len
            True -> V.removeElement watchers ix

-- | If we are decision level 0, we can use the facts we have asserted
-- at this level to simplify the clause database, including *problem
-- clauses*.
--
-- At decision level 0, we can remove clauses that have any True
-- literals.  We can remove all False literals from existing clauses.
simplifyClauses :: Solver ()
simplifyClauses = do
  dl <- getDecisionLevel
  case dl > 0 of
    True -> return ()
    False -> do
      e <- ask
      P.modifyRef' (eAtGround e) (+1)
      -- forLearnedClauses () $ \() ix cref c -> do
      --   c' <- simplifyClause c
      --   case c' of
      --     [] -> removeLearnedClause ix cref
      --     [l] -> do
      --       removeLearnedClause ix cref
      --       assertLiteral l noClause
      --     l1:rest@(l2:_) -> do
      --       let cl = C.clause l1 rest
      --           watch1Ix = cref * 2
      --           watch2Ix = watch1Ix + 1
      --       w1 <- GA.unsafeReadArray (eWatchedLiterals e) watch1Ix
      --       w2 <- GA.unsafeReadArray (eWatchedLiterals e) watch2Ix
      --       wl1 <- GA.unsafeReadArray (eClausesWatchingLiteral e) w1
      --       wl2 <- GA.unsafeReadArray (eClausesWatchingLiteral e) w2
      --       removeWatchedClause wl1 cref
      --       removeWatchedClause wl2 cref
      --       GA.unsafeWriteArray (eLearnedClauses e) ix cl
      --       GA.unsafeWriteArray (eWatchedLiterals e) (cref * 2) l1
      --       GA.unsafeWriteArray (eWatchedLiterals e) (cref * 2 + 1) l2
      --       wl1' <- GA.unsafeReadArray (eClausesWatchingLiteral e) l1
      --       wl2' <- GA.unsafeReadArray (eClausesWatchingLiteral e) l2
      --       V.push wl1' cref
      --       V.push wl2' cref

simplifyClause :: C.Clause -> Solver [L.Literal]
simplifyClause = undefined
