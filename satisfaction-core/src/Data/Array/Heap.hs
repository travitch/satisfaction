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
import qualified Data.Array.Dynamic as DA
import qualified Data.Array.MArray as MA
import Data.Bits
import Data.IORef
import Data.Ix ( Ix, rangeSize, inRange )

data Heap a e = Heap { hArray :: {-# UNPACK #-} !(DA.DArray a Int e)
                     , hIndices :: {-# UNPACK #-} !(DA.DArray a e Int)
                     , hSize :: {-# UNPACK #-} !(IORef Int)
                     , hLessThan :: e -> e -> IO Bool
                     }

invalidIndex :: Int
invalidIndex = -1

-- | Allocate a new heap, allocating enough space for all of the
-- elements in the given range.
new :: (MA.MArray a e IO, MA.MArray a Int IO, Ix e)
    => (e, e)
    -> (e -> e -> IO Bool)
    -> e
    -> IO (Heap a e)
new eltRange comparator invalidElement = do
  szRef <- newIORef 0
  indices <- DA.newArray eltRange invalidIndex
  arr <- DA.newArray (0, rangeSize eltRange) invalidElement
  return Heap { hArray = arr
              , hIndices = indices
              , hSize = szRef
              , hLessThan = comparator
              }

-- | Insert an element into the heap, growing if necessary
insert :: (MA.MArray a e IO, MA.MArray a Int IO, Ix e) => Heap a e -> e -> IO ()
insert h elt = do
  ensureStorage h elt
  unsafeInsert h elt

-- | Insert an element into the heap.  Throws an error if the element
-- will not fit in the already allocated storage.
unsafeInsert :: (MA.MArray a e IO, MA.MArray a Int IO, Ix e) => Heap a e -> e -> IO ()
unsafeInsert h elt = do
  curIndex <- DA.readArray (hIndices h) elt
  case curIndex of
    _ | curIndex /= invalidIndex -> return ()
      | otherwise -> do
          tailIndex <- readIORef szRef
          modifyIORef' szRef (+1)
          DA.writeArray arr tailIndex elt
          DA.writeArray eltIndex elt tailIndex
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
percolateUp :: (MA.MArray a e IO, MA.MArray a Int IO, Ix e) => Heap a e -> e -> Int -> IO ()
percolateUp h elt = go
  where
    go arrIx
      | arrIx == 0 = do
          DA.writeArray (hArray h) arrIx elt
          DA.writeArray (hIndices h) elt arrIx
      | otherwise = do
          let arr = hArray h
              parentIx = parentIndex arrIx
          parentVal <- DA.readArray arr parentIx
          res <- hLessThan h elt parentVal
          case res of
            False -> do
              -- At the right place
              DA.writeArray arr arrIx elt
              DA.writeArray (hIndices h) elt arrIx
            True -> do
              -- Swap and recurse
              DA.writeArray arr arrIx parentVal
              DA.writeArray (hIndices h) parentVal arrIx
              DA.writeArray arr parentIx elt
              DA.writeArray (hIndices h) elt parentIx
              go parentIx


-- | Take the maximum element from the heap (if any) and fix up the
-- heap invariant.
takeMin :: (MA.MArray a e IO, MA.MArray a Int IO, Ix e) => Heap a e -> IO (Maybe e)
takeMin h = do
  sz <- size h
  case sz of
    0 -> return Nothing
    _ -> do
      minElt <- DA.readArray (hArray h) 0
      DA.writeArray (hIndices h) minElt invalidIndex
      modifyIORef' (hSize h) (subtract 1)
      when (sz > 1) $ do
        let sz' = sz - 1
        lastElt <- DA.readArray (hArray h) sz'
        DA.writeArray (hArray h) 0 lastElt
        DA.writeArray (hIndices h) lastElt 0
        percolateDown h lastElt sz' 0
      return (Just minElt)

withSmaller :: (MA.MArray a e IO)
            => (e -> e -> IO Bool)
            -> DA.DArray a Int e
            -> Int
            -> Int
            -> e
            -> Int
            -> (Int -> e -> IO b)
            -> IO b
withSmaller (.<.) arr sz ix1 elt1 ix2 k
  | ix2 >= sz = k ix1 elt1
  | otherwise = do
      elt2 <- DA.readArray arr ix2
      elt1LT <- elt1 .<. elt2
      case elt1LT of
        True -> k ix1 elt1
        False -> k ix2 elt2
{-# INLINE withSmaller #-}

percolateDown :: (MA.MArray a e IO, MA.MArray a Int IO, Ix e) => Heap a e -> e -> Int -> Int -> IO ()
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
            DA.writeArray arr arrIx smallestElt
            DA.writeArray (hIndices h) smallestElt arrIx
            DA.writeArray arr smallestIx elt
            DA.writeArray (hIndices h) elt smallestIx
            go smallestIx

size :: Heap a e -> IO Int
size = readIORef . hSize
{-# INLINE size #-}

null :: Heap a e -> IO Bool
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
ensureStorage :: (MA.MArray a e IO, MA.MArray a Int IO, Ix e) => Heap a e -> e -> IO ()
ensureStorage h elt = do
  currentBounds@(currentLow, currentHigh) <- DA.getBounds (hIndices h)
  unless (inRange currentBounds elt) $ do
    let newBounds = (min currentLow elt, max currentHigh elt)
    DA.grow (hIndices h) newBounds
    DA.grow (hArray h) (0, rangeSize newBounds - 1)


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
