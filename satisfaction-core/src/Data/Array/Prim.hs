{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Arrays of values
module Data.Array.Prim (
  -- * Immutable arrays
  Array,
  fromList,
  array,
  elems,
  size,
  (!),
  unsafeIndex,
  thaw,
  unsafeThaw
  ) where

import GHC.Exts hiding ( fromList )

import Control.Monad.Prim
import Control.Monad.ST ( runST )
import Data.Array.Prim.Internal
import qualified Data.Array.Prim.Mutable as M
import qualified Data.Foldable as F
import Data.Function ( on )
import Data.Ix.Zero

fromList :: (IxZero i) => [a] -> Array i a
fromList elts = runST $ do
  marr <- M.newArray (length elts) undefined
  F.forM_ (zip ([0..] :: [Int]) elts) $ \(ix, elt) -> do
    M.unsafeWriteArray marr (fromZeroIndex ix) elt
  M.unsafeFreeze marr

array :: (IxZero i) => [(i, a)] -> Array i a
array bindings = runST $ do
  ma <- M.newArray_ (length bindings)
  F.forM_ bindings $ \(ix, elt) -> do
    M.unsafeWriteArray ma ix elt
  M.unsafeFreeze ma

size :: Array i a -> Int
size a = I# (sizeofArray# (unArray a))
{-# INLINE size #-}

(!) :: (IxZero i) => Array i a -> i -> a
(!) arr ix
  | size arr <= toZeroIndex ix = error "Data.Array.Prim.(!): Index out of range"
  | otherwise = unsafeIndex arr ix
{-# INLINE (!) #-}

unsafeIndex :: (IxZero i) => Array i a -> i -> a
unsafeIndex arr ix =
  case indexArray# (unArray arr) i of
    (# elt #) -> elt
  where
    !(I# i) = toZeroIndex ix
{-# INLINE unsafeIndex #-}

thaw :: (PrimMonad m) => Array i a -> m (MArray m i a)
thaw arr = primitive $ \s# -> do
  case thawArray# a zero (sizeofArray# a) s# of
    (# s'#, ma# #) -> (# s'#, MArray ma# #)
  where
    !(I# zero) = 0
    a = unArray arr

unsafeThaw :: (PrimMonad m) => Array i a -> m (MArray m i a)
unsafeThaw arr = primitive $ \s# -> do
  case unsafeThawArray# (unArray arr) s# of
    (# s'#, ma# #) -> (# s'#, MArray ma# #)

elems :: (IxZero i) => Array i a -> [a]
elems = F.toList

instance (IxZero i) => F.Foldable (Array i) where
  {-# INLINE foldr #-}
  {-# INLINE foldl' #-}
  foldr = afoldr
  foldl' = afoldl'

afoldr :: (IxZero i) => (a -> b -> b) -> b -> Array i a -> b
afoldr f seed arr = go 0
  where
    sz = size arr
    go ix | sz <= ix = seed
          | otherwise =
              let elt = unsafeIndex arr (fromZeroIndex ix)
              in f elt (go (ix + 1))
{-# INLINE afoldr #-}

afoldl' :: (IxZero i) => (b -> a -> b) -> b -> Array i a -> b
afoldl' f seed arr@(Array {}) = go 0 seed
  where
    sz = size arr
    go !ix acc | sz <= ix = acc
               | otherwise =
                   let !elt = unsafeIndex arr (fromZeroIndex ix)
                   in go (ix + 1) (f seed elt)
{-# INLINE afoldl' #-}

instance (Eq a, IxZero i) => Eq (Array i a) where
  (==) = on (==) F.toList

instance (Ord a, IxZero i) => Ord (Array i a) where
  compare = on compare F.toList

instance (Show a, IxZero i) => Show (Array i a) where
  show a = "fromList " ++ show (F.toList a)

