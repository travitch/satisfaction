{-# LANGUAGE MagicHash #-}
module Data.Array.Prim.Internal (
  Array(..),
  MArray(..)
  ) where

import GHC.Exts
import Control.Monad.Prim

data Array i a = Array { unArray :: Array# a }

data MArray m i a = MArray { unMArray :: MutableArray# (PrimState m) a }
