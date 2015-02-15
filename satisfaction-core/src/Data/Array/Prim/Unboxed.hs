{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Array.Prim.Unboxed (
  Array,
  fromList,
  array,
  elems,
  size,
  (!),
  unsafeIndex,
  thawArray,
  -- * Unbox
  Unbox
  ) where

import GHC.Exts hiding ( fromList )

import Control.Monad.Prim
import Control.Monad.ST ( runST )
import Data.Array.Prim.Unboxed.Internal
import qualified Data.Array.Prim.Unboxed.Mutable as M
import qualified Data.Foldable as F
import Data.Function ( on )
import Data.Ix.Zero
import Data.Unbox

fromList :: (Unbox a, IxZero i) => [a] -> Array i a
fromList elts = runST $ do
  ma <- M.newArray_ (length elts)
  F.forM_ (zip [0..] elts) $ \(ix :: Int, elt) -> do
    M.unsafeWriteArray ma (fromZeroIndex ix) elt
  M.unsafeFreeze ma

array :: (Unbox a, IxZero i) => [(i, a)] -> Array i a
array bindings = runST $ do
  ma <- M.newArray_ (length bindings)
  F.forM_ bindings $ \(ix, elt) -> do
    M.unsafeWriteArray ma ix elt
  M.unsafeFreeze ma

size :: Array i a -> Int
size = arraySize
{-# INLINE size #-}

(!) :: (Unbox a, IxZero i) => Array i a -> i -> a
(!) a i | size a <= toZeroIndex i = error "Data.Array.Prim.Unboxed.!: Index out of bounds"
        | otherwise = unsafeIndex a i
{-# INLINE (!) #-}

unsafeIndex :: (Unbox a, IxZero i) => Array i a -> i -> a
unsafeIndex a ix = unboxIndex (arrayStorage a) i
  where
    !(I# i) = toZeroIndex ix
{-# INLINE unsafeIndex #-}

thawArray :: (PrimMonad m, Unbox a, IxZero i)
             => Array i a
             -> m (MArray m i a)
thawArray a = do
  ma <- M.newArray_ (size a)
  F.forM_ (zip [0..] (F.toList a)) $ \(ix :: Int, elt) -> do
    M.unsafeWriteArray ma (fromZeroIndex ix) elt
  return ma

elems :: (IxZero i) => Array i a -> [a]
elems = F.toList

instance (IxZero i) => F.Foldable (Array i) where
  {-# INLINE foldr #-}
  {-# INLINE foldl' #-}
  foldr = afoldr
  foldl' = afoldl'

afoldr :: (IxZero i) => (a -> b -> b) -> b -> Array i a -> b
afoldr f seed arr@(Array {}) = go 0
  where
    sz = size arr
    go ix | sz <= ix = seed
          | otherwise =
              let !elt = unsafeIndex arr (fromZeroIndex ix)
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
