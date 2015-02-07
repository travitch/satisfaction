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
  removeElement
  ) where

import Control.Monad ( when )
import Data.IORef
import Data.Ix ( rangeSize )
import qualified Data.Array.Dynamic as DA
import qualified Data.Array.MArray as MA

data Vector a e = Vector { vArray :: {-# UNPACK #-} !(DA.DArray a Int e)
                         , vSize :: {-# UNPACK #-} !(IORef Int)
                         }

new :: (MA.MArray a e IO) => Int -> e -> IO (Vector a e)
new cap0 e = do
  sz <- newIORef 0
  a <- DA.newArray (0, cap0) e
  return Vector { vArray = a
                , vSize = sz
                }

size :: Vector a e -> IO Int
size v = readIORef (vSize v)
{-# INLINE size #-}

push :: (MA.MArray a e IO) => Vector a e -> e -> IO ()
push v e = do
  sz <- readIORef (vSize v)
  bounds <- DA.getBounds (vArray v)
  when (rangeSize bounds >= sz) $ do
    DA.grow (vArray v) (0, 2 * sz)
  unsafePush v e
{-# INLINE push #-}

unsafePush :: (MA.MArray a e IO) => Vector a e -> e -> IO ()
unsafePush v e = do
  sz <- readIORef (vSize v)
  DA.writeArray (vArray v) sz e
  modifyIORef' (vSize v) (+1)
{-# INLINE unsafePush #-}

-- | Pop up to @n@ elements.  Will not drop the size below zero.
pop :: Vector a e -> Int -> IO ()
pop v n = do
  sz <- readIORef (vSize v)
  writeIORef (vSize v) (max 0 (sz - n))
{-# INLINE pop #-}

-- | Remove an element by swapping it with the last element and then
-- popping.
--
-- This function is only valid for non-empty vectors.
removeElement :: (MA.MArray a e IO) => Vector a e -> Int -> IO ()
removeElement v ix = do
  sz <- size v
  lastElt <- readVector v (sz - 1)
  DA.writeArray (vArray v) ix lastElt
  pop v 1
{-# INLINE removeElement #-}

readVector :: (MA.MArray a e IO) => Vector a e -> Int -> IO e
readVector v ix = DA.readArray (vArray v) ix
{-# INLINE readVector #-}