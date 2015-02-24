{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module Data.Unbox (
  Unbox(..),
  Proxy(..)
  ) where

import GHC.Exts
import GHC.Int

#include "MachDeps.h"

data Proxy a = Proxy

class Unbox a where
  -- | The number of bytes occupied by an element of type @a@
  unboxBytes :: Proxy a -> Int
  -- | Read a single element from an immutable byte array
  unboxIndex :: ByteArray# -> Int# -> a
  -- | Write a single element to a mutable byte array
  unboxWrite :: MutableByteArray# s -> Int# -> a -> State# s -> State# s
  -- | Read a single element from a mutable byte array
  unboxRead :: MutableByteArray# s -> Int# -> State# s -> (# State# s, a #)

instance Unbox Int where
  {-# INLINE unboxBytes #-}
  unboxBytes = \_ -> wordBytes
  {-# INLINE unboxIndex #-}
  unboxIndex = \ba ix -> I# (indexIntArray# ba ix)
  {-# INLINE unboxWrite #-}
  unboxWrite = \mba ix (I# elt) s# -> writeIntArray# mba ix elt s#
  {-# INLINE unboxRead #-}
  unboxRead = \mba ix s# ->
    case readIntArray# mba ix s# of
      (# s'#, i# #) -> (# s'#, I# i# #)

instance Unbox Int8 where
  {-# INLINE unboxBytes #-}
  unboxBytes = \_ -> 1
  {-# INLINE unboxIndex #-}
  unboxIndex = \ba ix -> I8# (indexInt8Array# ba ix)
  {-# INLINE unboxWrite #-}
  unboxWrite = \mba ix (I8# elt) s# -> writeInt8Array# mba ix elt s#
  {-# INLINE unboxRead #-}
  unboxRead = \mba ix s# ->
    case readInt8Array# mba ix s# of
      (# s'#, i# #) -> (# s'#, I8# i# #)

instance Unbox Double where
  {-# INLINE unboxBytes #-}
  {-# INLINE unboxIndex #-}
  {-# INLINE unboxWrite #-}
  {-# INLINE unboxRead #-}
  unboxBytes = \_ -> 8
  unboxIndex = \ba ix -> D# (indexDoubleArray# ba ix)
  unboxWrite = \mba ix (D# elt) s# -> writeDoubleArray# mba ix elt s#
  unboxRead = \mba ix s# ->
    case readDoubleArray# mba ix s# of
      (# s'#, d# #) -> (# s'#, D# d# #)

instance Unbox Float where
  {-# INLINE unboxBytes #-}
  {-# INLINE unboxIndex #-}
  {-# INLINE unboxWrite #-}
  {-# INLINE unboxRead #-}
  unboxBytes = \_ -> 4
  unboxIndex = \ba ix -> F# (indexFloatArray# ba ix)
  unboxWrite = \mba ix (F# elt) s# -> writeFloatArray# mba ix elt s#
  unboxRead = \mba ix s# ->
    case readFloatArray# mba ix s# of
      (# s'#, f# #) -> (# s'#, F# f# #)

wordBytes :: Int
wordBytes = SIZEOF_HSWORD
