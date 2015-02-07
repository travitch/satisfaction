module Data.Ix.Unsafe (
  Ix0(..)
  ) where

import Data.Ix ( Ix )

-- | An unsafe variant of 'Ix' that permits converting to an array
-- index without consulting bounds.
class (Ix i) => Ix0 i where
  unsafeToIndex :: i -> Int

instance Ix0 Int where
  {-# INLINE unsafeToIndex #-}
  unsafeToIndex = id
