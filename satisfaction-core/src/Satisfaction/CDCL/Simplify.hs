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

import Control.Monad ( when )
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.List as L
import qualified Data.Ref.Prim as P

import qualified Satisfaction.CDCL.Clause as CL
import qualified Satisfaction.CDCL.Core as C
import Satisfaction.CDCL.Monad
import qualified Satisfaction.Formula.Literal as L

clauseIsLocked :: CL.Clause Solver -> Solver Bool
clauseIsLocked cl = do
  e <- ask
  wl1 <- CL.unsafeReadLiteral cl 0
  r1 <- GA.unsafeReadArray (eDecisionReasons e) (L.var wl1)
  return (r1 == Just cl)
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
          locked <- clauseIsLocked cl
          clAct <- CL.readActivity cl
          clSize <- CL.literalCount cl
          case locked || clAct > cutoffActivity || clSize == 2 of
            True -> go cutoffActivity (ix + 1) nLearned clauseVec clauseArr
            False -> do
              removeClause clauseVec ix
              go cutoffActivity ix (nLearned - 1) clauseVec clauseArr


forLearnedClauses :: a -> (a -> Int -> CL.Clause Solver -> Solver a) -> Solver a
forLearnedClauses a k = do
  e <- ask
  AT.foldMArray (eLearnedClauses e) a $ \ix cl a' -> do
    k a' ix cl

approximateMedian :: Int -> Solver Double
approximateMedian nLearned = do
  mstorage <- GA.newArray nLearned 0
  nActivities <- forLearnedClauses 0 $ \counter _arrix cl -> do
    activity <- CL.readActivity cl
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
simplifyVectorClauses :: forall arr . (GA.PrimMArray arr (CL.Clause Solver))
                      => Int
                      -- ^ Current index being processed
                      -> Int
                      -- ^ Total number of clauses in the vector
                      -> V.Vector PMA.MArray Solver Int (CL.Clause Solver)
                      -- ^ The vector of problem clauses
                      -> arr Solver Int (CL.Clause Solver)
                      -- ^ The backing array of problem clauses
                      -> Solver ()
simplifyVectorClauses clauseNo nClauses clauseVec clauseArr
  | clauseNo >= nClauses = return ()
  | otherwise = do
      c <- GA.unsafeReadArray clauseArr clauseNo
      nLits <- CL.literalCount c
      go c nLits 0
  where
    go c nLits litIx
      | litIx >= nLits =
        case () of
            _ | nLits == 0 -> error "Simplify produced an empty clause"
              | litIx == 0 -> do
                  -- If we have one literal left, that means it is unassigned
                  -- and we can assign it True right now (and then remove it).
                  -- We also have to unwatch the clause.
                  V.removeElement clauseVec clauseNo
                  l <- CL.unsafeReadLiteral c 0
                  unwatchLiteral c l
                  C.assertLiteral l Nothing
                  simplifyVectorClauses clauseNo (nClauses - 1) clauseVec clauseArr
              | otherwise ->
                  simplifyVectorClauses (clauseNo + 1) nClauses clauseVec clauseArr
      | otherwise = do
          l <- CL.unsafeReadLiteral c litIx
          v <- C.literalValue l
          case v of
            _ | v == L.liftedFalse -> do
                  -- We know that the literal must be false, so we
                  -- want to remove it from the clause
                  mNewLit <- CL.removeLiteral c l
                  -- If this literal was watched, we have to unwatch
                  -- it and watch its replacement (if there is one)
                  when (litIx < 2) $ do
                    unwatchLiteral c l
                    case mNewLit of
                      Just newLit -> watchLiteral c newLit
                      Nothing -> return ()
                  -- Since we removed a literal by swapping it out, we
                  -- have to examine this index again.
                  go c (nLits - 1) litIx
              | v == L.liftedTrue -> do
                  -- The clause is satisfied, so don't bother to mess
                  -- with it anymore.  We can remove it, though.
                  --
                  -- The first two literals (if there are two) are
                  -- watched.  We have to update the watchlists since
                  -- we'll be removing this clause.
                  removeClause clauseVec clauseNo
                  simplifyVectorClauses clauseNo (nClauses - 1) clauseVec clauseArr
              | otherwise -> go c nLits (litIx + 1)

removeClause :: (GA.PrimMArray a (CL.Clause Solver)) => V.Vector a Solver Int (CL.Clause Solver) -> Int -> Solver ()
removeClause clauseVec clauseNo = do
  cl <- V.unsafeReadVector clauseVec clauseNo
  V.removeElement clauseVec clauseNo
  litCount <- CL.literalCount cl
  when (litCount >= 1) $ do
    l0 <- CL.unsafeReadLiteral cl 0
    unwatchLiteral cl l0
  when (litCount >= 2) $ do
    l1 <- CL.unsafeReadLiteral cl 1
    unwatchLiteral cl l1

watchLiteral :: CL.Clause Solver -> L.Literal -> Solver ()
watchLiteral c l = do
  wls <- asks eClausesWatchingLiteral
  v <- GA.unsafeReadArray wls l
  V.push v c

unwatchLiteral :: CL.Clause Solver -> L.Literal -> Solver ()
unwatchLiteral c l = do
  wls <- asks eClausesWatchingLiteral
  v <- GA.unsafeReadArray wls l
  nClauses <- V.size v
  go v 0 nClauses
  where
    go v ix nClauses
      | ix >= nClauses = error ("Could not find literal " ++ show l ++ " in watchlist")
      | otherwise = do
          cl <- V.unsafeReadVector v ix
          case cl == c of
            False -> go v (ix + 1) nClauses
            True -> do
              V.unsafeWriteVector v ix sentinelClause
              V.removeElement v ix

sentinelClause :: CL.Clause Solver
sentinelClause = error "Simplifier sentinel clause"

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
      let probClauses = eProblemClauses e
          learnedClauses = eLearnedClauses e
      nClauses <- V.size probClauses
      nLearnedClauses <- V.size learnedClauses
      GA.withBackingArray probClauses (simplifyVectorClauses 0 nClauses probClauses)
      GA.withBackingArray learnedClauses (simplifyVectorClauses 0 nLearnedClauses learnedClauses)
