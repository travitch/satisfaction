{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Prim.Generic (
  PrimArray(..),
  PrimMArray(..),
  ArrayBacked(..),
  Sized(..)
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
  readArray :: (PrimMonad m, IxZero i) => a m i e -> i -> m e
  unsafeReadArray :: (PrimMonad m, IxZero i) => a m i e -> i -> m e
  writeArray :: (PrimMonad m, IxZero i) => a m i e -> i -> e -> m ()
  unsafeWriteArray :: (PrimMonad m, IxZero i) => a m i e -> i -> e -> m ()

class ArrayBacked a e where
  withBackingArray :: (PrimMonad m)
                   => a m i e
                   -> (forall arr . (PrimMArray arr e) => arr m i e -> m b)
                   -> m b

class Sized a e where
  size :: (PrimMonad m) => a m i e -> m Int

instance PrimArray PA.Array e where
  {-# INLINE elems #-}
  elems a = PA.elems a
  {-# INLINE (!) #-}
  a ! i = a PA.! i
  {-# INLINE unsafeIndex #-}
  unsafeIndex a i = PA.unsafeIndex a i
  {-# INLINE plength #-}
  plength a = PA.size a

instance (PUA.Unbox e) => PrimArray PUA.Array e where
  {-# INLINE elems #-}
  elems a = PUA.elems a
  {-# INLINE (!) #-}
  a ! i = a PUA.! i
  {-# INLINE unsafeIndex #-}
  unsafeIndex a i = PUA.unsafeIndex a i
  {-# INLINE plength #-}
  plength a = PUA.size a

instance PrimMArray PMA.MArray e where
  {-# INLINE readArray #-}
  {-# INLINE writeArray #-}
  {-# INLINE unsafeReadArray #-}
  {-# INLINE unsafeWriteArray #-}
  newArray n e = PMA.newArray n e
  newArray_ n = PMA.newArray_ n
  readArray a ix = PMA.readArray a ix
  unsafeReadArray a ix = PMA.unsafeReadArray a ix
  writeArray a ix elt = PMA.writeArray a ix elt
  unsafeWriteArray a ix elt = PMA.unsafeWriteArray a ix elt

instance ArrayBacked PMA.MArray e where
  withBackingArray a f = f a

instance Sized PMA.MArray e where
  size = PMA.size

instance (PUMA.Unbox e) => PrimMArray PUMA.MArray e where
  {-# INLINE readArray #-}
  {-# INLINE writeArray #-}
  {-# INLINE unsafeReadArray #-}
  {-# INLINE unsafeWriteArray #-}
  newArray n e = PUMA.newArray n e
  newArray_ n = PUMA.newArray_ n
  readArray a ix = PUMA.readArray a ix
  unsafeReadArray a ix = PUMA.unsafeReadArray a ix
  writeArray a ix elt = PUMA.writeArray a ix elt
  unsafeWriteArray a ix elt = PUMA.unsafeWriteArray a ix elt

instance (PUMA.Unbox e) => ArrayBacked PUMA.MArray e where
  withBackingArray a f = f a

instance Sized PUMA.MArray e where
  size = PUMA.size
