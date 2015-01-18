-- | Helpers for traversing 'Array's
module Data.Array.Traverse (
  foldArrayM,
  mapArrayM_
  ) where

import qualified Data.Array.IArray as A

foldArrayM :: (A.IArray a e) => (b -> Int -> e -> IO b) -> b -> a Int e -> IO b
foldArrayM f seed a =
  let (low, high) = A.bounds a
  in go low high seed
  where
    go low cur b | cur < low = return b
                 | otherwise = f b cur (a A.! cur) >>= go low (cur - 1)
{-# INLINE foldArrayM #-}

mapArrayM_ :: (A.IArray a e) => (Int -> e -> IO ()) -> a Int e -> IO ()
mapArrayM_ f a =
  let (low, high) = A.bounds a
  in go low high
  where
    go low cur | cur < low = return ()
               | otherwise = f cur (a A.! cur) >> go low (cur - 1)
{-# INLINE mapArrayM_ #-}

