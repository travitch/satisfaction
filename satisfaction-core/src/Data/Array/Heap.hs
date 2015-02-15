{-# LANGUAGE FlexibleContexts #-}
-- | An array-based binary min-heap in IO
module Data.Array.Heap (
  Heap,
  new,
  size,
  null,
  insert,
  unsafeInsert,
  ensureStorage,
  takeMin
  ) where

import Prelude hiding ( null )

import Control.Applicative
import Control.Monad ( unless, when )
import Control.Monad.Prim
import qualified Data.Array.Dynamic as DA
import qualified Data.Array.Dynamic.Unboxed as UDA
import qualified Data.Array.Prim.Generic as GA
import Data.Bits
import Data.Ref.Prim
import Data.Ix.Zero

data Heap m e = Heap { hArray :: DA.DArray m Int e
                     , hIndices :: UDA.DArray m e Int
                     , hSize :: Ref m Int
                     , hLessThan :: e -> e -> m Bool
                     }

invalidIndex :: Int
invalidIndex = -1

-- | Allocate a new heap, allocating enough space for all of the
-- elements in the given range.
new :: (PrimMonad m, IxZero e)
    => Int
    -> (e -> e -> m Bool)
    -> e
    -> m (Heap m e)
new capacity comparator invalidElement = do
  szRef <- newRef 0
  indices <- UDA.newArray capacity invalidIndex
  arr <- DA.newArray capacity invalidElement
  return Heap { hArray = arr
              , hIndices = indices
              , hSize = szRef
              , hLessThan = comparator
              }

-- | Insert an element into the heap, growing if necessary
insert :: (PrimMonad m, IxZero e) => Heap m e -> e -> m ()
insert h elt = do
  ensureStorage h elt
  unsafeInsert h elt

-- | Insert an element into the heap.  Throws an error if the element
-- will not fit in the already allocated storage.
unsafeInsert :: (PrimMonad m, IxZero e) => Heap m e -> e -> m ()
unsafeInsert h elt = do
  curIndex <- UDA.readArray (hIndices h) elt
  case curIndex of
    _ | curIndex /= invalidIndex -> return ()
      | otherwise -> do
          tailIndex <- readRef szRef
          modifyRef' szRef (+1)
          GA.writeArray arr tailIndex elt
          GA.writeArray eltIndex elt tailIndex
          percolateUp h elt tailIndex
  where
    szRef = hSize h
    arr = hArray h
    eltIndex = hIndices h

-- | Compute the index of the parent of the value at the given index.
parentIndex :: Int -> Int
parentIndex i = (i - 1) `shiftR` 1
{-# INLINE parentIndex #-}

leftIndex :: Int -> Int
leftIndex i = (i `shiftL` 1) + 1
{-# INLINE leftIndex #-}

rightIndex :: Int -> Int
rightIndex i = (i `shiftL` 1) + 2
{-# INLINE rightIndex #-}


-- | Rebuild the heap invariant by moving the element at the given
-- index into its proper place.
percolateUp :: (PrimMonad m, IxZero e) => Heap m e -> e -> Int -> m ()
percolateUp h elt = go
  where
    go arrIx
      | arrIx == 0 = do
          GA.writeArray (hArray h) arrIx elt
          GA.writeArray (hIndices h) elt arrIx
      | otherwise = do
          let arr = hArray h
              parentIx = parentIndex arrIx
          parentVal <- GA.readArray arr parentIx
          res <- hLessThan h elt parentVal
          case res of
            False -> do
              -- At the right place
              GA.writeArray arr arrIx elt
              GA.writeArray (hIndices h) elt arrIx
            True -> do
              -- Swap and recurse
              GA.writeArray arr arrIx parentVal
              GA.writeArray (hIndices h) parentVal arrIx
              GA.writeArray arr parentIx elt
              GA.writeArray (hIndices h) elt parentIx
              go parentIx


-- | Take the maximum element from the heap (if any) and fix up the
-- heap invariant.
takeMin :: (PrimMonad m, IxZero e) => Heap m e -> m (Maybe e)
takeMin h = do
  sz <- size h
  case sz of
    0 -> return Nothing
    _ -> do
      minElt <- GA.readArray (hArray h) 0
      GA.writeArray (hIndices h) minElt invalidIndex
      modifyRef' (hSize h) (subtract 1)
      when (sz > 1) $ do
        let sz' = sz - 1
        lastElt <- GA.readArray (hArray h) sz'
        GA.writeArray (hArray h) 0 lastElt
        GA.writeArray (hIndices h) lastElt 0
        percolateDown h lastElt sz' 0
      return (Just minElt)

withSmaller :: (PrimMonad m)
            => (e -> e -> m Bool)
            -> DA.DArray m Int e
            -> Int
            -> Int
            -> e
            -> Int
            -> (Int -> e -> m b)
            -> m b
withSmaller (.<.) arr sz ix1 elt1 ix2 k
  | ix2 >= sz = k ix1 elt1
  | otherwise = do
      elt2 <- GA.readArray arr ix2
      elt1LT <- elt1 .<. elt2
      case elt1LT of
        True -> k ix1 elt1
        False -> k ix2 elt2
{-# INLINE withSmaller #-}

percolateDown :: (PrimMonad m, IxZero e) => Heap m e -> e -> Int -> Int -> m ()
percolateDown h elt sz = go
  where
    go arrIx = do
      let leftIx = leftIndex arrIx
          rightIx = rightIndex arrIx
          arr = hArray h
          lt = hLessThan h
      withSmaller lt arr sz arrIx elt leftIx $ \smallerOfLeftIx smallerOfLeftElt -> do
        withSmaller lt arr sz smallerOfLeftIx smallerOfLeftElt rightIx $ \smallestIx smallestElt -> do
          -- The smallest element gets written to the current spot
          -- (arrIx).  If smallestIx is arrIx, we are done (we found
          -- the location of our percolated element).  Otherwise, we
          -- actually swapped the elements and need to recursively
          -- proceed.
          unless (smallestIx == arrIx) $ do
            GA.writeArray arr arrIx smallestElt
            GA.writeArray (hIndices h) smallestElt arrIx
            GA.writeArray arr smallestIx elt
            GA.writeArray (hIndices h) elt smallestIx
            go smallestIx

size :: (PrimMonad m) => Heap m e -> m Int
size = readRef . hSize
{-# INLINE size #-}

null :: (PrimMonad m) => Heap m e -> m Bool
null h = (==0) <$> size h
{-# INLINE null #-}

-- | Make sure we have enough storage available for the new element.
--
-- This can be called in conjunction with 'unsafeInsert' to improve
-- efficiency, avoiding extraneous bounds checks.
--
-- We maintain the invariant that the heap array is always large
-- enough to hold all of the elements in the current range of the
-- index array.  Since we start with that invariant satisfied at
-- construction time, we only need to enlarge either array if the new
-- element is outside of the range of the current index array.
ensureStorage :: (PrimMonad m, IxZero e) => Heap m e -> e -> m ()
ensureStorage h elt = do
  curSize <- UDA.size (hIndices h)
  unless (zix < curSize) $ do
    UDA.grow (hIndices h) newBounds
    DA.grow (hArray h) newBounds
  where
    zix = toZeroIndex elt
    newBounds = zix * 2


{- Note [Design]

This is a very simple implementation based on a growable dynamic
array.  The heap is parametric in the underlying array and element
type (to allow boxed or unboxed data).  The root (max element) is at
index 1.  Indexes are Ints for simplicity, and are not exposed to
callers at all.

We reserve an odd number of elements (a power of 2 plus one) to
account for keeping the root at 1.

For now, we are actually pre-allocating all of the required storage
for the heap.  In the future, we'll be growing.  Perhaps we can build
in some basic dumb growth right now

-}
