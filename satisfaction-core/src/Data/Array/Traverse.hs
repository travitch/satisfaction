-- | Helpers for traversing 'Array's
module Data.Array.Traverse (
  foldArrayM,
  mapArrayM_,
  forArrayM_,
  forMArray_,
  foldMArray
  ) where

import qualified Control.Monad.Prim as P
import qualified Data.Array.Prim.Generic as G
import Data.Ix.Zero

foldArrayM :: (G.PrimArray a e, Monad m) => (b -> Int -> e -> m b) -> b -> a Int e -> m b
foldArrayM f seed a =
  let high = G.plength a - 1
  in go 0 high seed
  where
    go cur high b | cur <= high = f b cur (G.unsafeIndex a cur) >>= go (cur + 1) high
                  | otherwise = return b
{-# INLINE foldArrayM #-}

mapArrayM_ :: (G.PrimArray a e, Monad m) => (Int -> e -> m ()) -> a Int e -> m ()
mapArrayM_ f a =
  let high = G.plength a - 1
  in go 0 high
  where
    go cur high | cur <= high = f cur (G.unsafeIndex a cur) >> go (cur + 1) high
                | otherwise = return ()
{-# INLINE mapArrayM_ #-}

forArrayM_ :: (G.PrimArray a e, Monad m) => a Int e -> (Int -> e -> m ()) -> m ()
forArrayM_ a f =
  let high = G.plength a - 1
  in go 0 high
  where
    go cur high | cur <= high = f cur (G.unsafeIndex a cur) >> go (cur + 1) high
                | otherwise = return ()
{-# INLINE forArrayM_ #-}

forMArray_ :: (P.PrimMonad m, IxZero i, G.ArrayBacked a e, G.Sized a e)
           => a m i e
           -> (i -> e -> m ())
           -> m ()
forMArray_ a f = do
  sz <- G.size a
  G.withBackingArray a (go 0 sz)
  where
    go cur sz a' | cur >= sz = return ()
                 | otherwise = do
                     let i = fromZeroIndex cur
                     elt <- G.unsafeReadArray a' i
                     f i elt
                     go (cur + 1) sz a'
{-# INLINE forMArray_ #-}

foldMArray :: (P.PrimMonad m, IxZero i, G.Sized a e, G.ArrayBacked a e)
           => a m i e
           -> s
           -> (i -> e -> s -> m s)
           -> m s
foldMArray a seed f = do
  sz <- G.size a
  G.withBackingArray a (go 0 seed sz)
  where
    go cur val sz arr | cur >= sz = return val
                      | otherwise = do
                          let i = fromZeroIndex cur
                          elt <- G.unsafeReadArray arr i
                          val' <- f i elt val
                          go (cur + 1) val' sz arr
{-# INLINE foldMArray #-}
