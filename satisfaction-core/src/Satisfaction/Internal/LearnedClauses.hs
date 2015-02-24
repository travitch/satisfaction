-- | These are utilities for dealing with learning and forgetting
-- learned clauses.
module Satisfaction.Internal.LearnedClauses (
  reduceLearnedClauses
  ) where

import Data.IORef

import qualified Data.Array.Heap as H
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.List as L

import qualified Satisfaction.CNF as C
import qualified Satisfaction.Internal.Literal as L
import Satisfaction.Internal.Monad

clauseIsLocked :: Env -> ClauseRef -> IO Bool
clauseIsLocked e cref = do
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
  nAssignments <- liftIO $ V.size (eDecisionStack e)
  nLearned <- liftIO $ readIORef (eLearnedClauseCount e)
  maxLearned <- liftIO $ readIORef (eMaxLearnedClauses e)
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
      liftIO $ modifyIORef (eLearnedCleanup e) (+1)
      amedian <- approximateMedian nLearned
      clauseInc <- liftIO $ readIORef (eClauseIncrement e)
      let cutoffActivity = max amedian (clauseInc / fromIntegral nLearned)
      forLearnedClauses () $ \() ix cref cl -> do
        locked <- clauseIsLocked e cref
        clAct <- GA.unsafeReadArray (eClauseActivity e) ix
        case locked || clAct > cutoffActivity || C.clauseSize cl == 2 of
          True -> return ()
          False -> do
            wl1 <- GA.unsafeReadArray (eWatchedLiterals e) (cref * 2)
            wl2 <- GA.unsafeReadArray (eWatchedLiterals e) (cref * 2 + 1)
            l1Watchers <- GA.unsafeReadArray (eClausesWatchingLiteral e) wl1
            l2Watchers <- GA.unsafeReadArray (eClausesWatchingLiteral e) wl2
            removeWatchedClause l1Watchers cref
            removeWatchedClause l2Watchers cref
            H.insert (eClauseRefPool e) ix
            modifyIORef' (eLearnedClauseCount e) (subtract 1)

forLearnedClauses :: a -> (a -> Int -> ClauseRef -> C.Clause -> IO a) -> Solver a
forLearnedClauses a k = do
  e <- ask
  nProblemClauses <- liftIO $ GA.size (eProblemClauses e)
  liftIO $ AT.foldMArray (eLearnedClauses e) a $ \ix cl a' -> do
    let cref = ix + nProblemClauses
    refIsAvailable <- H.member (eClauseRefPool e) ix
    case refIsAvailable of
      False -> k a' ix cref cl
      True -> return a'

approximateMedian :: Int -> Solver Double
approximateMedian nLearned = do
  e <- ask
  mstorage <- liftIO $ GA.newArray nLearned 0
  nActivities <- forLearnedClauses 0 $ \counter arrix _cref _cl -> do
    activity <- GA.unsafeReadArray (eClauseActivity e) arrix
    GA.unsafeWriteArray mstorage counter activity
    return (counter + 1)
  liftIO $ medianOfMedians nActivities mstorage

medianOfMedians :: Int
                -> PUMA.MArray IO Int Double
                -> IO Double
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

readFiveFrom :: Int -> PUMA.MArray IO Int Double -> IO [Double]
readFiveFrom ix0 arr = do
  sz <- GA.size arr
  go (min (ix0 + 4) (sz - 1)) sz []
  where
    go ix sz acc | ix < ix0 = return acc
                 | otherwise = do
                     elt <- GA.unsafeReadArray arr ix
                     go (ix - 1) sz (elt : acc)
{-# INLINE readFiveFrom #-}

medianOfFiveFrom :: Int -> PUMA.MArray IO Int Double -> IO Double
medianOfFiveFrom ix arr = do
  lst <- readFiveFrom ix arr
  case L.sort lst of
    _:_:v3:_:_:_ -> return v3
    _:v2:v3:_:_ -> return (v2 * 0.5 + v3 * 0.5)
    _:v2:_:_ -> return v2
    v1:v2:_ -> return (v1 * 0.5 + v2 * 0.5)
    v1:_ -> return v1
    [] -> error "Empty list in medianOfFiveFrom"

removeWatchedClause :: V.Vector PUMA.MArray IO ClauseRef -> ClauseRef -> IO ()
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
