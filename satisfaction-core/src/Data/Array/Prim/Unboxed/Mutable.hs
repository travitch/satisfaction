{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}
module Data.Array.Prim.Unboxed.Mutable (
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
  unsafeFreeze,
  -- * Unbox
  Unbox
  ) where

import GHC.Exts

import Control.Monad.Prim
import Data.Array.Prim.Unboxed.Internal
import qualified Data.Foldable as F
import Data.Ix.Zero
import Data.Unbox

newArray :: (PrimMonad m, Unbox a, IxZero i)
         => Int
         -> a
         -> m (MArray m i a)
newArray nElts elt0 = do
  ma <- newArray_ nElts
  F.forM_ [0..nElts - 1] $ \ix -> do
    unsafeWriteArray ma (fromZeroIndex ix) elt0
  return ma

newArray_ :: forall a i m . (PrimMonad m, Unbox a, IxZero i)
          => Int
          -> m (MArray m i a)
newArray_ nElts =
  primitive $ \s# -> do
    case newByteArray# bytes s# of
      (# s'#, a# #) -> (# s'#, MArray a# nElts #)
  where
    !(I# bytes) = nElts * unboxBytes (Proxy :: Proxy a)

size :: (PrimMonad m) => MArray m i a -> m Int
size = return . marraySize
{-# INLINE size #-}

readArray :: (PrimMonad m, Unbox a, IxZero i)
          => MArray m i a
          -> i
          -> m a
readArray marr ix
  | marraySize marr <= toZeroIndex ix = error "Data.Array.Prim.Unboxed.Mutable.readArray: Index out of bounds"
  | otherwise = unsafeReadArray marr ix
{-# INLINE readArray #-}

writeArray :: (PrimMonad m, Unbox a, IxZero i)
           => MArray m i a
           -> i
           -> a
           -> m ()
writeArray marr ix elt
  | marraySize marr <= toZeroIndex ix = error "Data.Array.Prim.Unboxed.Mutable.writeArray: Index out of bounds"
  | otherwise = unsafeWriteArray marr ix elt
{-# INLINE writeArray #-}

freeze :: forall a i m . (PrimMonad m, Unbox a)
               => MArray m i a
               -> m (Array i a)
freeze marr =
  primitive $ \s# -> do
    case newByteArray# bytes s# of
      (# s1#, dest# #) ->
        case copyMutableByteArray# (marrayStorage marr) 0# dest# 0# bytes s1# of
          s2# ->
            case unsafeFreezeByteArray# dest# s2# of
              (# s3#, a# #) -> (# s3#, Array a# nElts #)
  where
    nElts = marraySize marr
    !(I# bytes) = nElts * unboxBytes (Proxy :: Proxy a)

unsafeReadArray :: (PrimMonad m, Unbox a, IxZero i)
                => MArray m i a
                -> i
                -> m a
unsafeReadArray marr ix =
  primitive (\s# -> unboxRead (marrayStorage marr) i s#)
  where
    !(I# i) = toZeroIndex ix
{-# INLINE unsafeReadArray #-}

unsafeWriteArray :: (PrimMonad m, Unbox a, IxZero i)
                 => MArray m i a
                 -> i
                 -> a
                 -> m ()
unsafeWriteArray marr ix elt =
  primitive_ (\s# -> unboxWrite (marrayStorage marr) i elt s#)
  where
    !(I# i) = toZeroIndex ix
{-# INLINE unsafeWriteArray #-}

unsafeFreeze :: (PrimMonad m, Unbox a)
                     => MArray m i a
                     -> m (Array i a)
unsafeFreeze marr =
  primitive $ \s# -> do
    case unsafeFreezeByteArray# (marrayStorage marr) s# of
      (# s'#, a# #) -> (# s'#, Array a# (marraySize marr) #)

