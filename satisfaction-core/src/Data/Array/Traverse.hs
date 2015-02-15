-- | Helpers for traversing 'Array's
module Data.Array.Traverse (
  foldArrayM,
  mapArrayM_
  ) where

import qualified Data.Array.Prim.Generic as G

foldArrayM :: (G.PrimArray a e, Monad m) => (b -> Int -> e -> m b) -> b -> a Int e -> m b
foldArrayM f seed a =
  let high = G.plength a - 1
  in go 0 high seed
  where
    go low cur b | cur < low = return b
                 | otherwise = f b cur (G.unsafeIndex a cur) >>= go low (cur - 1)
{-# INLINE foldArrayM #-}

mapArrayM_ :: (G.PrimArray a e, Monad m) => (Int -> e -> m ()) -> a Int e -> m ()
mapArrayM_ f a =
  let high = G.plength a - 1
  in go 0 high
  where
    go low cur | cur < low = return ()
               | otherwise = f cur (G.unsafeIndex a cur) >> go low (cur - 1)
{-# INLINE mapArrayM_ #-}

