{-# LANGUAGE FlexibleContexts #-}
-- | Vectors built on top of dynamic arrays.
--
-- These vectors support amortized constant push and pop at the end.
-- Elements can be removed efficiently from the middle by swapping
-- with the last element and then popping.
module Data.Array.Vector.Unboxed (
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
import qualified Data.Array.Dynamic.Unboxed as DA

data Vector m e = Vector { vArray :: DA.DArray m Int e
                         , vSize :: Ref m Int
                         }

new :: (PrimMonad m, DA.Unbox e) => Int -> e -> m (Vector m e)
new cap0 e = do
  sz <- newRef 0
  a <- DA.newArray cap0 e
  return Vector { vArray = a
                , vSize = sz
                }

size :: (PrimMonad m) => Vector m e -> m Int
size v = readRef (vSize v)
{-# INLINE size #-}

push :: (PrimMonad m, DA.Unbox e) => Vector m e -> e -> m ()
push v e = do
  sz <- readRef (vSize v)
  capacity <- DA.size (vArray v)
  when (capacity <= sz) $ do
    DA.grow (vArray v) (2 * sz)
  unsafePush v e
{-# INLINE push #-}

unsafePush :: (PrimMonad m, DA.Unbox e) => Vector m e -> e -> m ()
unsafePush v e = do
  sz <- readRef (vSize v)
  DA.unsafeWriteArray (vArray v) sz e
  modifyRef' (vSize v) (+1)
{-# INLINE unsafePush #-}

-- | Pop up to @n@ elements.  Will not drop the size below zero.
pop :: (PrimMonad m, DA.Unbox e) => Vector m e -> Int -> m ()
pop v n = do
  sz <- readRef (vSize v)
  writeRef (vSize v) (max 0 (sz - n))
{-# INLINE pop #-}

-- | Remove an element by swapping it with the last element and then
-- popping.
--
-- This function is only valid for non-empty vectors.
removeElement :: (PrimMonad m, DA.Unbox e) => Vector m e -> Int -> m ()
removeElement v ix = do
  sz <- size v
  lastElt <- readVector v (sz - 1)
  DA.writeArray (vArray v) ix lastElt
  pop v 1
{-# INLINE removeElement #-}

readVector :: (PrimMonad m, DA.Unbox e) => Vector m e -> Int -> m e
readVector v ix = DA.readArray (vArray v) ix
{-# INLINE readVector #-}

unsafeReadVector :: (PrimMonad m, DA.Unbox e) => Vector m e -> Int -> m e
unsafeReadVector v ix = DA.unsafeReadArray (vArray v) ix
{-# INLINE unsafeReadVector #-}
