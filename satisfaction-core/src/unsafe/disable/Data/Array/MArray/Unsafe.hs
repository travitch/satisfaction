module Data.Array.MArray.Unsafe (
  readArray,
  writeArray
  ) where

import qualified Data.Array.MArray as MA
import Data.Ix.Unsafe ( Ix0 )

readArray :: (Ix0 i, MA.MArray a e m) => a i e -> i -> m e
readArray = MA.readArray
{-# INLINE readArray #-}

writeArray :: (Ix0 i, MA.MArray a e m) => a i e -> i -> e -> m ()
writeArray = MA.writeArray
{-# INLINE writeArray #-}
