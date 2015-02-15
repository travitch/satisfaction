-- | A class for zero-based indexing
--
-- This is to map newtypes of integral types to a zero-based index
module Data.Ix.Zero (
  IxZero(..)
  ) where

class IxZero a where
  toZeroIndex :: a -> Int
  fromZeroIndex :: Int -> a

instance IxZero Int where
  {-# INLINE toZeroIndex #-}
  toZeroIndex = id
  {-# INLINE fromZeroIndex #-}
  fromZeroIndex = id
