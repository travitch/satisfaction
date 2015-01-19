{-# LANGUAGE FlexibleContexts #-}
-- | An implementation of a dynamic (growable) array in IO
module Data.Array.Dynamic (
  DArray,
  newArray,
  newArray_,
  readArray,
  writeArray,
  getBounds,
  grow,
  ) where

import qualified Data.Foldable as F
import Data.IORef
import Data.Ix ( Ix, range )
import qualified Data.Array.MArray as MA

-- | A dynamically growable mutable array
data DArray a i e = DArray { daArray :: {-# UNPACK #-} !(IORef (a i e))
                           }

-- | Allocate a new array, reserving the given amount of storage
newArray_ :: (MA.MArray a e IO, Ix i) => (i, i) -> IO (DArray a i e)
newArray_ reserve = do
  a <- MA.newArray_ reserve
  aref <- newIORef a
  return $ DArray { daArray = aref
                  }

newArray :: (MA.MArray a e IO, Ix i) => (i, i) -> e -> IO (DArray a i e)
newArray reserve def = do
  a <- MA.newArray reserve def
  aref <- newIORef a
  return $ DArray { daArray = aref
                  }

readArray :: (MA.MArray a e IO, Ix i) => DArray a i e -> i -> IO e
readArray da i = do
  a <- readIORef (daArray da)
  MA.readArray a i
{-# INLINE readArray #-}

writeArray :: (MA.MArray a e IO, Ix i) => DArray a i e -> i -> e -> IO ()
writeArray da i e = do
  a <- readIORef (daArray da)
  MA.writeArray a i e
{-# INLINE writeArray #-}

getBounds :: (MA.MArray a e IO, Ix i) => DArray a i e -> IO (i, i)
getBounds da = do
  a <- readIORef (daArray da)
  MA.getBounds a
{-# INLINE getBounds #-}

-- | Grow the array to the max-union of the old bounds and the new bounds.
--
-- The values at the new indexes are undefined.  Values at the old
-- indexes remain the same.
grow :: (MA.MArray a e IO, Ix i) => DArray a i e -> (i, i) -> IO ()
grow da oldBounds@(newLower, newUpper) = do
  (oldLower, oldUpper) <- getBounds da
  let newBounds = (min oldLower newLower, max oldUpper newUpper)
  case newBounds == oldBounds of
    True -> return ()
    False -> do
      a0 <- readIORef (daArray da)
      a1 <- MA.newArray_ newBounds
      copyElements a0 a1 oldBounds
      writeIORef (daArray da) a1

copyElements :: (MA.MArray a e m, Ix i)
             => a i e
             -> a i e
             -> (i, i)
             -> m ()
copyElements a0 a1 r =
  F.forM_ (range r) $ \ix -> do
    e <- MA.readArray a0 ix
    MA.writeArray a1 ix e

