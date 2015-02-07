module Data.Array.MArray.Unsafe (
  readArray,
  writeArray
  ) where

import qualified Data.Array.Base as BA
import Data.Ix.Unsafe ( Ix0(..) )

readArray :: (Ix0 i, BA.MArray a e m) => a i e -> i -> m e
readArray a i = BA.unsafeRead a (unsafeToIndex i)
{-# INLINE readArray #-}

writeArray :: (Ix0 i, BA.MArray a e m) => a i e -> i -> e -> m ()
writeArray a i e = BA.unsafeWrite a (unsafeToIndex i) e
{-# INLINE writeArray #-}
