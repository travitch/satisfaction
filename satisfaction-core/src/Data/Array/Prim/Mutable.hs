{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module Data.Array.Prim.Mutable (
  MArray,
  newArray,
  newArray_,
  size,
  readArray,
  writeArray,
  freeze,
  -- * Unsafe interface
  unsafeReadArray,
  unsafeWriteArray,
  unsafeFreeze
  ) where

import GHC.Exts

import Control.Monad.Prim
import Data.Array.Prim.Internal
import Data.Ix.Zero

-- | Allocate a new array
--
-- Calls 'error' if the size is negative
newArray :: (PrimMonad m) => Int -> a -> m (MArray m i a)
newArray (I# sz) elt0 = primitive $ \s# -> do
  case newArray# sz elt0 s# of
    (# s'#, arr #) -> (# s'#, MArray arr #)

newArray_ :: (PrimMonad m) => Int -> m (MArray m i a)
newArray_ ix = newArray ix undefined

readArray :: (PrimMonad m, IxZero i) => MArray m i a -> i -> m a
readArray marr ix
  | ix' < 0 || pureSize marr <= ix' = error "Data.Array.Prim.Mutable.readArray: Index out of bounds"
  | otherwise = unsafeReadArray marr ix
  where
    ix' = toZeroIndex ix
{-# INLINE readArray #-}

unsafeReadArray :: (PrimMonad m, IxZero i) => MArray m i a -> i -> m a
unsafeReadArray marr ix =
  primitive (\s# -> readArray# (unMArray marr) i s#)
  where
    !(I# i) = toZeroIndex ix
{-# INLINE unsafeReadArray #-}

writeArray :: (PrimMonad m, IxZero i) => MArray m i a -> i -> a -> m ()
writeArray marr ix elt
  | ix' < 0 || pureSize marr <= ix' = error "Data.Array.Prim.Mutable.writeArray: Index out of bounds"
  | otherwise = unsafeWriteArray marr ix elt
  where
    ix' = toZeroIndex ix
{-# INLINE writeArray #-}

unsafeWriteArray :: (PrimMonad m, IxZero i) => MArray m i a -> i -> a -> m ()
unsafeWriteArray marr ix elt =
  primitive_ (\s# -> writeArray# (unMArray marr) i elt s#)
  where
    !(I# i) = toZeroIndex ix
{-# INLINE unsafeWriteArray #-}

size :: (PrimMonad m) => MArray m i a -> m Int
size = return . pureSize
{-# INLINE size #-}

pureSize :: MArray s i a -> Int
pureSize marr = I# (sizeofMutableArray# (unMArray marr))
{-# INLINE pureSize #-}

freeze :: (PrimMonad m) => MArray m i a -> m (Array i a)
freeze marr = primitive $ \s# -> do
  case freezeArray# arr 0# (sizeofMutableArray# arr) s# of
    (# s'#, a# #) -> (# s'#, Array a# #)
  where
    arr = unMArray marr

unsafeFreeze :: (PrimMonad m) => MArray m i a -> m (Array i a)
unsafeFreeze marr = primitive $ \s# -> do
  case unsafeFreezeArray# (unMArray marr) s# of
    (# s'#, a# #) -> (# s'#, Array a# #)

