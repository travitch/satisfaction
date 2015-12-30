{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
-- | These are utilities for simplifying the clause database.
--
-- This includes 1) dealing with learning and forgetting learned
-- clauses and 2) simplifying clauses when we backtrack to the ground
-- level.
module Satisfaction.CDCL.Simplify (
  reduceLearnedClauses,
  simplifyClauses
  ) where

import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.List as L
import qualified Data.Ref.Prim as P

import Satisfaction.CDCL.Monad
import qualified Satisfaction.CDCL.Core as C
import qualified Satisfaction.CDCL.Constraint as CO

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
    False -> removeInactiveClauses
{-# INLINE reduceLearnedClauses #-}

-- | One approach would be to sort here.  Due to the watchlist
-- representation, sorting would be complicated.  Instead, we use the
-- median-of-medians algorithm to find an approximate median and throw
-- out all of the clauses with less activity than that.
removeInactiveClauses :: Solver ()
removeInactiveClauses = do
  e <- ask
  let learnedClauses = eLearnedClauses e
  nLearnedClauses <- V.size learnedClauses
  case nLearnedClauses == 0 of
    True -> return ()
    False -> do
      P.modifyRef' (eLearnedCleanup e) (+1)
      amedian <- approximateMedian nLearnedClauses
      clauseInc <- P.readRef (eClauseIncrement e)
      let cutoffActivity = max amedian (clauseInc / fromIntegral nLearnedClauses)
      GA.withBackingArray learnedClauses (go cutoffActivity 0 nLearnedClauses learnedClauses)
  where
    go cutoffActivity ix nLearned clauseVec clauseArr
      | ix >= nLearned = return ()
      | otherwise = do
          cl <- GA.unsafeReadArray clauseArr ix
          locked <- CO.constraintIsLocked cl
          clAct <- CO.constraintReadActivity cl
          alwaysKeep <- CO.constraintAlwaysKeep cl
          case locked || clAct > cutoffActivity || alwaysKeep of
            True -> go cutoffActivity (ix + 1) nLearned clauseVec clauseArr
            False -> do
              removeConstraint clauseVec ix
              go cutoffActivity ix (nLearned - 1) clauseVec clauseArr


forLearnedClauses :: a -> (a -> Int -> Constraint -> Solver a) -> Solver a
forLearnedClauses a k = do
  e <- ask
  AT.foldMArray (eLearnedClauses e) a $ \ix cl a' -> do
    k a' ix cl

approximateMedian :: Int -> Solver Double
approximateMedian nLearned = do
  mstorage <- GA.newArray nLearned 0
  nActivities <- forLearnedClauses 0 $ \counter _arrix cl -> do
    activity <- CO.constraintReadActivity cl
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

-- | Simplify a clause in place (by mutating it).
--
-- This function handles updating watches as necessary and removing
-- the clause if it is reduced to one literal (or has any True
-- literals).  We can remove False literals.
--
-- When a clause is removed, the problem clause vector is updated
-- (i.e. shrunk).  We also pass in the backing array directly to save
-- a pointer dereference to read each clause.  The two won't get out
-- of sync because we never shrink a dynamic array.
simplifyVectorConstraints :: forall arr . (GA.PrimMArray arr Constraint)
                           => Int
                           -- ^ Total number of constraints in the vector
                           -> V.Vector PMA.MArray Solver Int Constraint
                           -- ^ The vector of problem clauses
                           -> arr Solver Int Constraint
                           -- ^ The backing array of problem clauses
                           -> Solver ()
simplifyVectorConstraints nConstraints0 conVec conArr =
  go 0 nConstraints0
  where
    go ix nConstraints
      | ix >= nConstraints = return ()
      | otherwise = do
          con <- GA.unsafeReadArray conArr ix
          shouldRemove <- CO.constraintSimplify con
          case shouldRemove of
            False -> go (ix + 1) nConstraints
            True -> do
              CO.constraintRemove con
              V.removeElement conVec ix
              go ix (nConstraints - 1)

removeConstraint :: (GA.PrimMArray a Constraint) => V.Vector a Solver Int Constraint -> Int -> Solver ()
removeConstraint clauseVec clauseNo = do
  cl <- V.unsafeReadVector clauseVec clauseNo
  CO.constraintRemove cl
  V.removeElement clauseVec clauseNo

-- | If we are decision level 0, we can use the facts we have asserted
-- at this level to simplify the clause database, including *problem
-- clauses*.
--
-- At decision level 0, we can remove clauses that have any True
-- literals.  We can remove all False literals from existing clauses.
simplifyClauses :: Solver ()
simplifyClauses = do
  dl <- C.getDecisionLevel
  case dl > 0 of
    True -> return ()
    False -> do
      e <- ask
      P.modifyRef' (eAtGround e) (+1)
      let probClauses = eProblemClauses e
          learnedClauses = eLearnedClauses e
      nClauses <- V.size probClauses
      nLearnedClauses <- V.size learnedClauses
      GA.withBackingArray probClauses (simplifyVectorConstraints nClauses probClauses)
      GA.withBackingArray learnedClauses (simplifyVectorConstraints nLearnedClauses learnedClauses)
