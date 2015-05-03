{-# LANGUAGE FlexibleContexts #-}
-- | An array-based binary min-heap in IO
module Data.Array.Heap (
  Heap,
  new,
  size,
  null,
  member,
  insert,
  unsafeInsert,
  unsafeUpdate,
  ensureStorage,
  takeMin
  ) where

import Control.Applicative
import Control.Monad ( unless, when )
import Control.Monad.Prim
import qualified Data.Array.Dynamic as DA
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import Data.Bits
import Data.Ref.Prim
import Data.Ix.Zero

import Prelude hiding ( null )

data Heap a m e = Heap { hArray :: DA.DArray a m Int e
                       , hIndices :: DA.DArray PUMA.MArray m e Int
                       , hSize :: Ref m Int
                       , hLessThan :: e -> e -> m Bool
                       }

invalidIndex :: Int
invalidIndex = -1

-- | Allocate a new heap, allocating enough space for all of the
-- elements in the given range.
new :: (PrimMonad m, GA.PrimMArray a e, IxZero e)
    => Int
    -> (e -> e -> m Bool)
    -> e
    -> m (Heap a m e)
new capacity comparator invalidElement = do
  szRef <- newRef 0
  indices <- DA.newArray capacity invalidIndex
  arr <- DA.newArray capacity invalidElement
  return Heap { hArray = arr
              , hIndices = indices
              , hSize = szRef
              , hLessThan = comparator
              }

-- | Test if an element is in the heap
member :: (PrimMonad m, GA.PrimMArray a e, IxZero e)
       => Heap a m e
       -> e
       -> m Bool
member h elt = do
  sz <- GA.size (hIndices h)
  case toZeroIndex elt < sz of
    False -> return False
    True -> do
      ix <- GA.unsafeReadArray (hIndices h) elt
      return (ix /= invalidIndex)
{-# INLINE member #-}

-- | Insert an element into the heap, growing if necessary
insert :: (PrimMonad m, GA.PrimMArray a e, IxZero e, GA.Sized a e) => Heap a m e -> e -> m ()
insert h elt = do
  ensureStorage h elt
  unsafeInsert h elt
{-# INLINABLE insert #-}

-- | Insert an element into the heap.  Throws an error if the element
-- will not fit in the already allocated storage.
unsafeInsert :: (PrimMonad m, GA.PrimMArray a e, IxZero e) => Heap a m e -> e -> m ()
unsafeInsert h elt = do
  curIndex <- DA.unsafeReadArray (hIndices h) elt
  case curIndex of
    _ | curIndex /= invalidIndex -> return ()
      | otherwise -> do
          tailIndex <- readRef szRef
          modifyRef' szRef (+1)
          GA.unsafeWriteArray arr tailIndex elt
          GA.unsafeWriteArray eltIndex elt tailIndex
          percolateUp h elt tailIndex
  where
    szRef = hSize h
    arr = hArray h
    eltIndex = hIndices h
{-# INLINABLE unsafeInsert #-}

unsafeUpdate :: (PrimMonad m, GA.PrimMArray a e, IxZero e) => Heap a m e -> e -> m ()
unsafeUpdate h elt = do
  curIndex <- DA.unsafeReadArray (hIndices h) elt
  case curIndex of
    _ | curIndex == invalidIndex -> unsafeInsert h elt
      | otherwise -> do
          percolateUp h elt curIndex
          ix' <- DA.unsafeReadArray (hIndices h) elt
          sz <- size h
          percolateDown h elt ix' sz
{-# INLINABLE unsafeUpdate #-}

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
percolateUp :: (PrimMonad m, GA.PrimMArray a e, IxZero e) => Heap a m e -> e -> Int -> m ()
percolateUp h elt = go
  where
    go arrIx
      | arrIx == 0 = do
          GA.unsafeWriteArray (hArray h) arrIx elt
          GA.unsafeWriteArray (hIndices h) elt arrIx
      | otherwise = do
          let arr = hArray h
              parentIx = parentIndex arrIx
          parentVal <- GA.unsafeReadArray arr parentIx
          res <- hLessThan h elt parentVal
          case res of
            False -> do
              -- At the right place
              GA.unsafeWriteArray arr arrIx elt
              GA.unsafeWriteArray (hIndices h) elt arrIx
            True -> do
              -- Swap and recurse
              GA.unsafeWriteArray arr arrIx parentVal
              GA.unsafeWriteArray (hIndices h) parentVal arrIx
              GA.unsafeWriteArray arr parentIx elt
              GA.unsafeWriteArray (hIndices h) elt parentIx
              go parentIx


-- | Take the maximum element from the heap (if any) and fix up the
-- heap invariant.
takeMin :: (PrimMonad m, GA.PrimMArray a e, IxZero e) => Heap a m e -> m (Maybe e)
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
{-# INLINEABLE takeMin #-}

withSmaller :: (PrimMonad m, GA.PrimMArray a e)
            => (e -> e -> m Bool)
            -> DA.DArray a m Int e
            -> Int
            -> Int
            -> e
            -> Int
            -> (Int -> e -> m b)
            -> m b
withSmaller (.<.) arr sz ix1 elt1 ix2 k
  | ix2 >= sz = k ix1 elt1
  | otherwise = do
      elt2 <- GA.unsafeReadArray arr ix2
      elt1LT <- elt1 .<. elt2
      case elt1LT of
        True -> k ix1 elt1
        False -> k ix2 elt2
{-# INLINE withSmaller #-}

percolateDown :: (PrimMonad m, GA.PrimMArray a e, IxZero e) => Heap a m e -> e -> Int -> Int -> m ()
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
            GA.unsafeWriteArray arr arrIx smallestElt
            GA.unsafeWriteArray (hIndices h) smallestElt arrIx
            GA.unsafeWriteArray arr smallestIx elt
            GA.unsafeWriteArray (hIndices h) elt smallestIx
            go smallestIx

size :: (PrimMonad m, GA.PrimMArray a e) => Heap a m e -> m Int
size = readRef . hSize
{-# INLINE size #-}

null :: (PrimMonad m, GA.PrimMArray a e) => Heap a m e -> m Bool
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
ensureStorage :: (PrimMonad m, GA.PrimMArray a e, IxZero e, GA.Sized a e) => Heap a m e -> e -> m ()
ensureStorage h elt = do
  curSize <- DA.size (hIndices h)
  unless (zix < curSize) $ do
    DA.grow (hIndices h) newBounds
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
