{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
-- | An implementation of a dynamic (growable) array in IO
module Data.Array.Dynamic.Unboxed (
  DArray,
  newArray,
  newArray_,
  readArray,
  writeArray,
  size,
  grow,
  unsafeReadArray,
  unsafeWriteArray,
  PUMA.Unbox
  ) where

import Control.Monad.Prim
import qualified Data.Foldable as F
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import Data.Ix.Zero
import Data.Ref.Prim

-- | A dynamically growable mutable array
newtype DArray m i e =
  DArray { daArray :: Ref m (PUMA.MArray m i e)
         }

instance (PUMA.Unbox e) => GA.PrimMArray DArray e where
  {-# INLINE readArray #-}
  {-# INLINE writeArray #-}
  {-# INLINE unsafeReadArray #-}
  {-# INLINE unsafeWriteArray #-}
  {-# INLINE size #-}
  newArray_ = newArray_
  newArray = newArray
  readArray = readArray
  writeArray = writeArray
  unsafeReadArray = unsafeReadArray
  unsafeWriteArray = unsafeWriteArray
  size = size

-- | Allocate a new array, reserving the given amount of storage
newArray_ :: (PrimMonad m, IxZero i, PUMA.Unbox e) => Int -> m (DArray m i e)
newArray_ len = do
  a <- PUMA.newArray_ len
  aref <- newRef a
  return $ DArray { daArray = aref
                  }

newArray :: (PrimMonad m, IxZero i, PUMA.Unbox e) => Int -> e -> m (DArray m i e)
newArray reserve def = do
  a <- PUMA.newArray reserve def
  aref <- newRef a
  return $ DArray { daArray = aref
                  }

readArray :: (PrimMonad m, IxZero i, PUMA.Unbox e) => DArray m i e -> i -> m e
readArray da i = do
  a <- readRef (daArray da)
  PUMA.readArray a i
{-# INLINE readArray #-}

unsafeReadArray :: (PrimMonad m, IxZero i, PUMA.Unbox e) => DArray m i e -> i -> m e
unsafeReadArray da i = do
  a <- readRef (daArray da)
  PUMA.unsafeReadArray a i
{-# INLINE unsafeReadArray #-}

writeArray :: (PrimMonad m, IxZero i, PUMA.Unbox e) => DArray m i e -> i -> e -> m ()
writeArray da i e = do
  a <- readRef (daArray da)
  PUMA.writeArray a i e
{-# INLINE writeArray #-}

unsafeWriteArray :: (PrimMonad m, IxZero i, PUMA.Unbox e) => DArray m i e -> i -> e -> m ()
unsafeWriteArray da i e = do
  a <- readRef (daArray da)
  PUMA.unsafeWriteArray a i e
{-# INLINE unsafeWriteArray #-}

size :: (PrimMonad m) => DArray m i e -> m Int
size da = do
  a <- readRef (daArray da)
  PUMA.size a
{-# INLINE size #-}

-- | Grow the array to the max-union of the old bounds and the new bounds.
--
-- The values at the new indexes are undefined.  Values at the old
-- indexes remain the same.
grow :: (PrimMonad m, IxZero i, PUMA.Unbox e) => DArray m i e -> Int -> m ()
grow da newSize = do
  oldSize <- size da
  case newSize > oldSize of
    False -> return ()
    True -> do
      a0 <- readRef (daArray da)
      a1 <- PUMA.newArray_ newSize
      copyElements a0 a1 oldSize
      writeRef (daArray da) a1

copyElements :: (PrimMonad m, IxZero i, PUMA.Unbox e)
             => PUMA.MArray m i e
             -> PUMA.MArray m i e
             -> Int
             -> m ()
copyElements a0 a1 oldSize =
  F.forM_ [0..oldSize - 1] $ \(fromZeroIndex -> ix) -> do
    e <- PUMA.readArray a0 ix
    PUMA.writeArray a1 ix e


