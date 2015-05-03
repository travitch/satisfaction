{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | Vectors built on top of dynamic arrays.
--
-- These vectors support amortized constant push and pop at the end.
-- Elements can be removed efficiently from the middle by swapping
-- with the last element and then popping.
module Data.Array.Vector (
  Vector,
  new,
  size,
  push,
  unsafePush,
  pop,
  clear,
  readVector,
  unsafeReadVector,
  writeVector,
  unsafeWriteVector,
  removeElement,
  unsafeRemoveElement
  ) where

import Control.Monad ( when )
import Control.Monad.Prim
import Data.Ix.Zero
import Data.Ref.Prim
import qualified Data.Array.Dynamic as DA
import qualified Data.Array.Prim.Generic as GA

data Vector a m i e = Vector { vArray :: DA.DArray a m i e
                             , vSize :: Ref m Int
                             }

instance (GA.PrimMArray a e) => GA.Sized (Vector a) e where
  size = size

instance (GA.ArrayBacked a e) => GA.ArrayBacked (Vector a) e where
  withBackingArray a f = GA.withBackingArray (vArray a) f

-- instance GA.ArrayBacked Vector a where
--   withBackingArray v f = GA.withBackingArray (vArray v) f

new :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Int -> e -> m (Vector a m i e)
new cap0 e = do
  sz <- newRef 0
  a <- DA.newArray cap0 e
  return Vector { vArray = a
                , vSize = sz
                }

size :: (PrimMonad m, GA.PrimMArray a e) => Vector a m i e -> m Int
size v = readRef (vSize v)
{-# INLINE size #-}

push :: (PrimMonad m, GA.PrimMArray a e, GA.Sized a e, IxZero i) => Vector a m i e -> e -> m ()
push v e = do
  sz <- readRef (vSize v)
  capacity <- GA.size (vArray v)
  when (capacity <= sz) $ do
    DA.grow (vArray v) (2 * sz)
  unsafePush v e
{-# INLINE push #-}

unsafePush :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Vector a m i e -> e -> m ()
unsafePush v e = do
  sz <- readRef (vSize v)
  GA.unsafeWriteArray (vArray v) (fromZeroIndex sz) e
  modifyRef' (vSize v) (+1)
{-# INLINE unsafePush #-}

-- | Pop up to @n@ elements.  Will not drop the size below zero.
pop :: (PrimMonad m, GA.PrimMArray a e) => Vector a m i e -> Int -> m ()
pop v n = do
  sz <- readRef (vSize v)
  writeRef (vSize v) (max 0 (sz - n))
{-# INLINE pop #-}

clear :: (PrimMonad m, GA.PrimMArray a e) => Vector a m i e -> m ()
clear v = writeRef (vSize v) 0
{-# INLINE clear #-}

-- | Remove an element by swapping it with the last element and then
-- popping.
--
-- This function is only valid for non-empty vectors.
removeElement :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Vector a m i e -> i -> m ()
removeElement v ix = do
  sz <- size v
  lastElt <- readVector v (fromZeroIndex (sz - 1))
  GA.writeArray (vArray v) ix lastElt
  pop v 1
{-# INLINE removeElement #-}

unsafeRemoveElement :: (PrimMonad m, GA.PrimMArray a e, IxZero i, GA.ArrayBacked a e) => Vector a m i e -> i -> m ()
unsafeRemoveElement v ix = do
  sz <- size v
  GA.withBackingArray (vArray v) $ \arr -> do
    lastElt <- GA.unsafeReadArray arr (fromZeroIndex (sz - 1))
    GA.unsafeWriteArray arr ix lastElt
  pop v 1
{-# INLINE unsafeRemoveElement #-}

readVector :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Vector a m i e -> i -> m e
readVector v ix = GA.readArray (vArray v) ix
{-# INLINE readVector #-}

unsafeReadVector :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Vector a m i e -> i -> m e
unsafeReadVector v ix = GA.unsafeReadArray (vArray v) ix
{-# INLINE unsafeReadVector #-}

writeVector :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Vector a m i e -> i -> e -> m ()
writeVector v ix e = GA.writeArray (vArray v) ix e
{-# INLINE writeVector #-}

unsafeWriteVector :: (PrimMonad m, GA.PrimMArray a e, IxZero i) => Vector a m i e -> i -> e -> m ()
unsafeWriteVector v ix e = GA.unsafeWriteArray (vArray v) ix e
{-# INLINE unsafeWriteVector #-}
