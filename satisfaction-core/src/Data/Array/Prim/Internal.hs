{-# LANGUAGE MagicHash #-}
module Data.Array.Prim.Internal (
  Array(..),
  MArray(..)
  ) where

import GHC.Exts
import Control.Monad.Prim

data Array i e = Array { unArray :: Array# e }

data MArray m i e = MArray { unMArray :: MutableArray# (PrimState m) e }
