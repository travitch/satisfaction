{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Array.Prim.Generic (
  PrimArray(..),
  PrimMArray(..)
  ) where

import Control.Monad.Prim
import qualified Data.Array.Prim as PA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Prim.Unboxed as PUA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import Data.Ix.Zero

class PrimArray a e where
  elems :: (IxZero i) => a i e -> [e]
  (!) :: (IxZero i) => a i e -> i -> e
  unsafeIndex :: (IxZero i) => a i e -> i -> e
  plength :: a i e -> Int

class PrimMArray a e where
  newArray :: (PrimMonad m, IxZero i) => Int -> e -> m (a m i e)
  newArray_ :: (PrimMonad m, IxZero i) => Int -> m (a m i e)
  size :: (PrimMonad m) => a m i e -> m Int
  readArray :: (PrimMonad m, IxZero i) => a m i e -> i -> m e
  unsafeReadArray :: (PrimMonad m, IxZero i) => a m i e -> i -> m e
  writeArray :: (PrimMonad m, IxZero i) => a m i e -> i -> e -> m ()
  unsafeWriteArray :: (PrimMonad m, IxZero i) => a m i e -> i -> e -> m ()

instance PrimArray PA.Array e where
  {-# INLINE elems #-}
  elems = PA.elems
  {-# INLINE (!) #-}
  a ! i = a PA.! i
  {-# INLINE unsafeIndex #-}
  unsafeIndex = PA.unsafeIndex
  {-# INLINE plength #-}
  plength = PA.size

instance (PUA.Unbox e) => PrimArray PUA.Array e where
  {-# INLINE elems #-}
  elems = PUA.elems
  {-# INLINE (!) #-}
  a ! i = a PUA.! i
  {-# INLINE unsafeIndex #-}
  unsafeIndex = PUA.unsafeIndex
  {-# INLINE plength #-}
  plength = PUA.size

instance PrimMArray PMA.MArray e where
  {-# INLINE size #-}
  {-# INLINE readArray #-}
  {-# INLINE writeArray #-}
  {-# INLINE unsafeReadArray #-}
  {-# INLINE unsafeWriteArray #-}
  newArray = PMA.newArray
  newArray_ = PMA.newArray_
  size = PMA.size
  readArray = PMA.readArray
  unsafeReadArray = PMA.unsafeReadArray
  writeArray = PMA.writeArray
  unsafeWriteArray = PMA.unsafeWriteArray

instance (PUMA.Unbox e) => PrimMArray PUMA.MArray e where
  {-# INLINE size #-}
  {-# INLINE readArray #-}
  {-# INLINE writeArray #-}
  {-# INLINE unsafeReadArray #-}
  {-# INLINE unsafeWriteArray #-}
  newArray = PUMA.newArray
  newArray_ = PUMA.newArray_
  size = PUMA.size
  readArray = PUMA.readArray
  unsafeReadArray = PUMA.unsafeReadArray
  writeArray = PUMA.writeArray
  unsafeWriteArray = PUMA.unsafeWriteArray
