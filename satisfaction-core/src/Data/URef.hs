{-# LANGUAGE FlexibleContexts #-}
-- | Simple and efficient unboxed refs
module Data.URef (
  IOURef,
  newIOURef,
  readIOURef,
  writeIOURef,
  modifyIOURef'
  ) where

import qualified Data.Array.Base as BA
import qualified Data.Array.IO as IOA

newtype IOURef a = IOURef { ioRefStorage :: IOA.IOUArray Int a }

newIOURef :: (IOA.MArray IOA.IOUArray a IO) => a -> IO (IOURef a)
newIOURef a = do
  arr <- IOA.newArray (0, 0) a
  return $! IOURef { ioRefStorage = arr }

readIOURef :: (IOA.MArray IOA.IOUArray a IO) => IOURef a -> IO a
readIOURef r = BA.unsafeRead (ioRefStorage r) 0
{-# INLINE readIOURef #-}

writeIOURef :: (IOA.MArray IOA.IOUArray a IO) => IOURef a -> a -> IO ()
writeIOURef r a = BA.unsafeWrite (ioRefStorage r) 0 a
{-# INLINE writeIOURef #-}

modifyIOURef' :: (IOA.MArray IOA.IOUArray a IO) => IOURef a -> (a -> a) -> IO ()
modifyIOURef' r f = do
  v <- readIOURef r
  writeIOURef r (f v)
{-# INLINE modifyIOURef' #-}
