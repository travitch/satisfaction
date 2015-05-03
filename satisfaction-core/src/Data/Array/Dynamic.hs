{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
-- | An implementation of a dynamic (growable) array in IO
module Data.Array.Dynamic (
  DArray,
  newArray,
  newArray_,
  readArray,
  writeArray,
  size,
  grow,
  unsafeReadArray,
  unsafeWriteArray
  ) where

import Control.Monad.Prim
import qualified Data.Foldable as F
import qualified Data.Array.Prim.Generic as GA
import Data.Ix.Zero
import Data.Ref.Prim

-- | A dynamically growable mutable array
newtype DArray a m i e =
  DArray { daArray :: Ref m (a m i e)
         }

instance (GA.PrimMArray a e) => GA.PrimMArray (DArray a) e where
  {-# INLINE readArray #-}
  {-# INLINE writeArray #-}
  {-# INLINE unsafeReadArray #-}
  {-# INLINE unsafeWriteArray #-}
  newArray_ n = newArray_ n
  newArray n e = newArray n e
  readArray a ix = readArray a ix
  writeArray a ix elt = writeArray a ix elt
  unsafeReadArray a ix = unsafeReadArray a ix
  unsafeWriteArray a ix elt = unsafeWriteArray a ix elt

instance (GA.Sized a e) => GA.Sized (DArray a) e where
  size a = size a

instance (GA.ArrayBacked a e) => GA.ArrayBacked (DArray a) e where
  withBackingArray da f = do
    a <- readRef (daArray da)
    GA.withBackingArray a f

-- | Allocate a new array, reserving the given amount of storage
newArray_ :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Int -> m (DArray a m i e)
newArray_ len = do
  a <- GA.newArray_ len
  aref <- newRef a
  return $ DArray { daArray = aref
                  }

newArray :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Int -> e -> m (DArray a m i e)
newArray reserve def = do
  a <- GA.newArray reserve def
  aref <- newRef a
  return $ DArray { daArray = aref
                  }

readArray :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => DArray a m i e -> i -> m e
readArray da i = do
  a <- readRef (daArray da)
  GA.readArray a i
{-# INLINE readArray #-}

unsafeReadArray :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => DArray a m i e -> i -> m e
unsafeReadArray da i = do
  a <- readRef (daArray da)
  GA.unsafeReadArray a i
{-# INLINE unsafeReadArray #-}

writeArray :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => DArray a m i e -> i -> e -> m ()
writeArray da i e = do
  a <- readRef (daArray da)
  GA.writeArray a i e
{-# INLINE writeArray #-}

unsafeWriteArray :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => DArray a m i e -> i -> e -> m ()
unsafeWriteArray da i e = do
  a <- readRef (daArray da)
  GA.unsafeWriteArray a i e
{-# INLINE unsafeWriteArray #-}

size :: (PrimMonad m, GA.Sized a e) => DArray a m i e -> m Int
size da = do
  a <- readRef (daArray da)
  GA.size a
{-# INLINE size #-}

-- | Grow the array to the max-union of the old bounds and the new bounds.
--
-- The values at the new indexes are undefined.  Values at the old
-- indexes remain the same.
grow :: (PrimMonad m, GA.PrimMArray a e, IxZero i, GA.Sized a e) => DArray a m i e -> Int -> m ()
grow da newSize = do
  oldSize <- size da
  case newSize > oldSize of
    False -> return ()
    True -> do
      a0 <- readRef (daArray da)
      a1 <- GA.newArray_ newSize
      copyElements a0 a1 oldSize
      writeRef (daArray da) a1

copyElements :: (PrimMonad m, GA.PrimMArray a e, IxZero i)
             => a m i e
             -> a m i e
             -> Int
             -> m ()
copyElements a0 a1 oldSize =
  F.forM_ [0..oldSize - 1] $ \(fromZeroIndex -> ix) -> do
    e <- GA.readArray a0 ix
    GA.writeArray a1 ix e

