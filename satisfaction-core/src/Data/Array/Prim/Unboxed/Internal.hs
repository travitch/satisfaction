{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MagicHash #-}
module Data.Array.Prim.Unboxed.Internal (
  Array(..),
  MArray(..)
  ) where

import GHC.Exts
import Control.Monad.Prim
import Data.Unbox ( Unbox )

data Array i a = Unbox a => Array { arrayStorage :: ByteArray#
                                  , arraySize :: Int
                                  }

data MArray m i a = MArray { marrayStorage :: MutableByteArray# (PrimState m)
                           , marraySize :: Int
                           }

