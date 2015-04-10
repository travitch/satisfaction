{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main ( main ) where

import Control.DeepSeq
import qualified Criterion.Main as C
import qualified Data.Array.IO as IOA
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Primitive.Mutable as PMV
import qualified Data.Vector.Unboxed.Mutable as UMV

-- import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Dynamic as DA
import Data.Unbox

main :: IO ()
main = C.defaultMain benchmarks

benchmarks :: [C.Benchmark]
benchmarks = [
  C.bgroup "Primitive Mutable Array of Int" [
      withPMA $ \a -> C.bench "PMA.readArray" (C.whnfIO (PMA.readArray a 2))
      , withPMA $ \a -> C.bench "PMA.unsafeReadArray" (C.whnfIO (PMA.unsafeReadArray a 2))
      , withPMA $ \a -> C.bench "PMA.writeArray" (C.whnfIO (PMA.writeArray a 1 2))
      , withPMA $ \a -> C.bench "PMA.unsafeWriteArray" (C.whnfIO (PMA.unsafeWriteArray a 1 2))
      ],
  C.bgroup "Primitive Unboxed Mutable Array of Int" [
      withPUMA $ \a -> C.bench "PUMA.readArray" (C.whnfIO (PUMA.readArray a 2))
      , withPUMA $ \a -> C.bench "PUMA.unsafeReadArray" (C.whnfIO (PUMA.unsafeReadArray a 2))
      , withPUMA $ \a -> C.bench "PUMA.writeArray" (C.whnfIO (PUMA.writeArray a 1 2))
      , withPUMA $ \a -> C.bench "PUMA.unsafeWriteArray" (C.whnfIO (PUMA.unsafeWriteArray a 1 2))
      ],
  C.bgroup "Dynamic PUMA of Int" [
    withDA $ \a -> C.bench "DA.readArray" (C.whnfIO (DA.readArray a 2))
    , withDA $ \a -> C.bench "DA.unsafeReadArray" (C.whnfIO (DA.unsafeReadArray a 1))
    , withDA $ \a -> C.bench "DA.writeArray" (C.whnfIO (DA.writeArray a 1 2))
    , withDA $ \a -> C.bench "DA.unsafeWriteArray" (C.whnfIO (DA.unsafeWriteArray a 1 2))
    ],
  C.bgroup "Data.Array.IOUArray Array of Int" [
    withIOA $ \a -> C.bench "IOA.readArray" (C.whnfIO (IOA.readArray a 2))
    , withIOA $ \a -> C.bench "IOA.writeArray" (C.whnfIO (IOA.writeArray a 1 2))
    ],
  C.bgroup "Mutable Vector of Int" [
    withMV $ \a -> C.bench "MV.read" (C.whnfIO (MV.read a 2))
    , withMV $ \a -> C.bench "MV.unsafeRead" (C.whnfIO (MV.unsafeRead a 2))
    , withMV $ \a -> C.bench "MV.write" (C.whnfIO (MV.write a 1 2))
    , withMV $ \a -> C.bench "MV.unsafeWrite" (C.whnfIO (MV.unsafeWrite a 1 2))
    ],
  C.bgroup "Prim Mutable Vector of Int" [
    withPMV $ \a -> C.bench "PMV.read" (C.whnfIO (PMV.read a 2))
    , withPMV $ \a -> C.bench "PMV.unsafeRead" (C.whnfIO (PMV.unsafeRead a 2))
    , withPMV $ \a -> C.bench "PMV.write" (C.whnfIO (PMV.write a 1 2))
    , withPMV $ \a -> C.bench "PMV.unsafeWrite" (C.whnfIO (PMV.unsafeWrite a 1 2))
    ],
  C.bgroup "Unboxed Mutable Vector of Int" [
    withUMV $ \a -> C.bench "UMV.read" (C.whnfIO (UMV.read a 2))
    , withUMV $ \a -> C.bench "UMV.unsafeRead" (C.whnfIO (UMV.unsafeRead a 2))
    , withUMV $ \a -> C.bench "UMV.write" (C.whnfIO (UMV.write a 1 2))
    , withUMV $ \a -> C.bench "UMV.unsafeWrite" (C.whnfIO (UMV.unsafeWrite a 1 2))
    ]
  ]

withPMA :: (PMA.MArray IO Int Int -> C.Benchmark) -> C.Benchmark
withPMA = C.env (PMA.newArray 100 0)

withPUMA :: (PUMA.MArray IO Int Int -> C.Benchmark) -> C.Benchmark
withPUMA = C.env (PUMA.newArray_ 100)

withIOA :: (IOA.IOUArray Int Int -> C.Benchmark) -> C.Benchmark
withIOA = C.env (IOA.newArray_ (0, 100))

withMV :: (MV.IOVector Int -> C.Benchmark) -> C.Benchmark
withMV = C.env (MV.replicate 100 0)

withPMV :: (PMV.IOVector Int -> C.Benchmark) -> C.Benchmark
withPMV = C.env (PMV.replicate 100 0)

withUMV :: (UMV.IOVector Int -> C.Benchmark) -> C.Benchmark
withUMV = C.env (UMV.replicate 100 0)

withDA :: (DA.DArray PUMA.MArray IO Int Int -> C.Benchmark) -> C.Benchmark
withDA = C.env (DA.newArray_ 100)

instance NFData (PUMA.MArray IO i e) where
  rnf _ = ()

instance NFData (PMA.MArray IO i e) where
  rnf _ = ()

instance NFData (DA.DArray a IO i e) where
  rnf _ = ()

instance NFData (IOA.IOUArray i e) where
  rnf _ = ()

instance NFData (MV.IOVector a) where
  rnf _ = ()


newtype NT = NT Int
           deriving (Eq, Ord, Show, Unbox)
