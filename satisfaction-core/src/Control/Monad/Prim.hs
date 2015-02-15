{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
-- | An abstraction over Monads implementing state threads (IO and ST)
--
-- Note that it also provides mutable references through the PrimRef
-- class.
module Control.Monad.Prim (
  PrimMonad(..),
  primitive_
  ) where

import GHC.IO ( IO(..) )
import GHC.Exts
import GHC.ST ( ST(..) )
import Control.Applicative
import Data.Ref.Prim

class (Applicative m, Monad m, PrimRef m) => PrimMonad m where
  type PrimState m
  primitive :: (State# (PrimState m) -> (# State# (PrimState m), a #)) -> m a

instance PrimMonad IO where
  type PrimState IO = RealWorld
  {-# INLINE primitive #-}
  primitive = IO

instance PrimMonad (ST s) where
  type PrimState (ST s) = s
  {-# INLINE primitive #-}
  primitive = ST


primitive_ :: (PrimMonad m)
           => (State# (PrimState m) -> State# (PrimState m))
           -> m ()
primitive_ f = primitive (\s# -> (# f s#, () #))
{-# INLINE primitive_ #-}
