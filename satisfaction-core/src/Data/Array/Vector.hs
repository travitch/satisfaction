{-# LANGUAGE FlexibleContexts #-}
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
  readVector,
  unsafeReadVector,
  removeElement
  ) where

import Control.Monad ( when )
import Control.Monad.Prim
import Data.Ref.Prim
import qualified Data.Array.Dynamic as DA
import qualified Data.Array.Prim.Generic as GA

data Vector a m e = Vector { vArray :: DA.DArray a m Int e
                           , vSize :: Ref m Int
                           }

new :: (PrimMonad m, GA.PrimMArray a e) => Int -> e -> m (Vector a m e)
new cap0 e = do
  sz <- newRef 0
  a <- DA.newArray cap0 e
  return Vector { vArray = a
                , vSize = sz
                }

size :: (PrimMonad m, GA.PrimMArray a e) => Vector a m e -> m Int
size v = readRef (vSize v)
{-# INLINE size #-}

push :: (PrimMonad m, GA.PrimMArray a e) => Vector a m e -> e -> m ()
push v e = do
  sz <- readRef (vSize v)
  capacity <- GA.size (vArray v)
  when (capacity <= sz) $ do
    DA.grow (vArray v) (2 * sz)
  unsafePush v e
{-# INLINE push #-}

unsafePush :: (PrimMonad m, GA.PrimMArray a e) => Vector a m e -> e -> m ()
unsafePush v e = do
  sz <- readRef (vSize v)
  GA.unsafeWriteArray (vArray v) sz e
  modifyRef' (vSize v) (+1)
{-# INLINE unsafePush #-}

-- | Pop up to @n@ elements.  Will not drop the size below zero.
pop :: (PrimMonad m, GA.PrimMArray a e) => Vector a m e -> Int -> m ()
pop v n = do
  sz <- readRef (vSize v)
  writeRef (vSize v) (max 0 (sz - n))
{-# INLINE pop #-}

-- | Remove an element by swapping it with the last element and then
-- popping.
--
-- This function is only valid for non-empty vectors.
removeElement :: (PrimMonad m, GA.PrimMArray a e) => Vector a m e -> Int -> m ()
removeElement v ix = do
  sz <- size v
  lastElt <- readVector v (sz - 1)
  GA.writeArray (vArray v) ix lastElt
  pop v 1
{-# INLINE removeElement #-}

readVector :: (PrimMonad m, GA.PrimMArray a e) => Vector a m e -> Int -> m e
readVector v ix = GA.readArray (vArray v) ix
{-# INLINE readVector #-}

unsafeReadVector :: (PrimMonad m, GA.PrimMArray a e) => Vector a m e -> Int -> m e
unsafeReadVector v ix = GA.unsafeReadArray (vArray v) ix
{-# INLINE unsafeReadVector #-}
