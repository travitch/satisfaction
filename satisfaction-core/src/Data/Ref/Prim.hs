{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
-- | Abstract over Refs (IORef, STRef) in a generic PrimRef Monad.
--
-- This allows code that uses references to be generic over the state
-- thread Monad.
module Data.Ref.Prim (
  PrimRef(..)
  ) where

import Control.Monad.ST ( ST )
import qualified Data.IORef as IO
import qualified Data.STRef as ST

class (Monad m) => PrimRef m where
  type Ref m :: * -> *
  newRef :: a -> m (Ref m a)
  readRef :: Ref m a -> m a
  writeRef :: Ref m a -> a -> m ()
  modifyRef' :: Ref m a -> (a -> a) -> m ()

instance PrimRef IO where
  type Ref IO = IO.IORef
  {-# INLINE newRef #-}
  {-# INLINE readRef #-}
  {-# INLINE writeRef #-}
  {-# INLINE modifyRef' #-}
  newRef = IO.newIORef
  readRef = IO.readIORef
  writeRef = IO.writeIORef
  modifyRef' = IO.modifyIORef'

instance PrimRef (ST s) where
  type Ref (ST s) = ST.STRef s
  {-# INLINE newRef #-}
  {-# INLINE readRef #-}
  {-# INLINE writeRef #-}
  {-# INLINE modifyRef' #-}
  newRef = ST.newSTRef
  readRef = ST.readSTRef
  writeRef = ST.writeSTRef
  modifyRef' = ST.modifySTRef'
