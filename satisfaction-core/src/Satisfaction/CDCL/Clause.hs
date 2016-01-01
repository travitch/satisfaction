{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
-- | The definition of clauses used in the solver
--
-- The main feature of these clauses is that they are mutable in IO,
-- and store metadata contiguously with literals.  See Note [Clause
-- Format] for details on the representation.
module Satisfaction.CDCL.Clause (
  Clause,
  new,
  readIsLearned,
  setLearnedFlag,
  literalCount,
  readActivity,
  writeActivity,
  readLiteral,
  unsafeReadLiteral,
  writeLiteral,
  unsafeWriteLiteral,
  forLiterals_,
  swapLiterals,
  unsafeSwapLiterals,
  removeLiteral
  ) where

import GHC.Exts
import GHC.Word

import Control.Applicative
import Data.Bits
import qualified Data.Foldable as F

import Prelude

import qualified Control.Monad.Prim as P
import qualified Satisfaction.Formula.Literal as L

-- | A clause with metadata mutable in IO
data Clause m = Clause (MutableByteArray# (P.PrimState m))

instance Eq (Clause m) where
  (Clause b1) == (Clause b2) = isTrue# (sameMutableByteArray# b1 b2)

new :: (P.PrimMonad m) => Double -> [L.Literal] -> m (Clause m)
new !activity lits
  | nLits <= 1 = error ("Creating singleton or empty clause: " ++ show lits)
  | otherwise = do
    c <- P.primitive $ \s0# -> do
      case newByteArray# nBytes# s0# of
        (# s1#, arr# #) -> (# s1#, Clause arr# #)
    writeFlags c 0
    writeLiteralCount c nLits
    writeActivity c activity
    F.forM_ (zip [0..] lits) $ \(ix, l) -> do
      unsafeWriteLiteral c ix l
    return c
  where
    !nLits@(I# nLits#) = length lits
    -- The fixed overhead (i.e., bytes for non-literal data) is 8 + 2
    -- + 2 = 12
    nBytes# = (nLits# *# 4#) +# 12#

readFlags :: (P.PrimMonad m) => Clause m -> m Word16
readFlags (Clause bytes) =
  P.primitive $ \s0# -> do
    case readWord16Array# bytes 5# s0# of
      (# s1#, w# #) -> (# s1#, W16# w# #)
{-# INLINE readFlags #-}

writeFlags :: (P.PrimMonad m) => Clause m -> Word16 -> m ()
writeFlags (Clause bytes) (W16# w#) =
  P.primitive_ $ writeWord16Array# bytes 5# w#
{-# INLINE writeFlags #-}

learnedFlagBit :: Int
learnedFlagBit = 1

readIsLearned :: (P.PrimMonad m) => Clause m -> m Bool
readIsLearned c = (`testBit` learnedFlagBit) <$> readFlags c
{-# INLINE readIsLearned #-}

setLearnedFlag :: (P.PrimMonad m) => Clause m -> m ()
setLearnedFlag c = do
  flgs <- readFlags c
  writeFlags c (flgs `setBit` learnedFlagBit)
{-# INLINE setLearnedFlag #-}

literalCount :: (P.PrimMonad m) => Clause m -> m Int
literalCount (Clause bytes) =
  P.primitive $ \s0# -> do
    case readInt16Array# bytes 4# s0# of
      (# s1#, i# #) -> (# s1#, I# i# #)
{-# INLINE literalCount #-}

writeLiteralCount :: (P.PrimMonad m) => Clause m -> Int -> m ()
writeLiteralCount (Clause bytes) (I# i#) =
  P.primitive_ $ \s0# -> do
    writeInt16Array# bytes 4# i# s0#
{-# INLINE writeLiteralCount #-}

readActivity :: (P.PrimMonad m) => Clause m -> m Double
readActivity (Clause bytes) =
  P.primitive $ \s0# -> do
    case readDoubleArray# bytes 0# s0# of
      (# s1#, d# #) -> (# s1#, D# d# #)
{-# INLINE readActivity #-}

writeActivity :: (P.PrimMonad m) => Clause m -> Double -> m ()
writeActivity (Clause bytes) (D# d#) =
  P.primitive_ $ \s# -> writeDoubleArray# bytes 0# d# s#
{-# INLINE writeActivity #-}

unsafeReadLiteral :: (P.PrimMonad m) => Clause m -> Int -> m L.Literal
unsafeReadLiteral (Clause bytes) (I# i#) = do
  P.primitive $ \s0# -> do
    case readInt32Array# bytes (i# +# 3#) s0# of
      (# s1#, l# #) -> (# s1#, L.MkLiteral (I# l#) #)
{-# INLINE unsafeReadLiteral #-}

readLiteral :: (P.PrimMonad m) => Clause m -> Int -> m L.Literal
readLiteral c i = do
  lc <- literalCount c
  case i < lc && i >= 0 of
    False -> error ("Clause.readLiteral index out of bounds: " ++ show i)
    True -> unsafeReadLiteral c i

unsafeWriteLiteral :: (P.PrimMonad m) => Clause m -> Int -> L.Literal -> m ()
unsafeWriteLiteral (Clause bytes) !(I# litNum#) (L.MkLiteral (I# lit#)) =
  P.primitive_ $ \s0# -> writeInt32Array# bytes (litNum# +# 3#) lit# s0#
{-# INLINE unsafeWriteLiteral #-}

writeLiteral :: (P.PrimMonad m) => Clause m -> Int -> L.Literal -> m ()
writeLiteral c i l = do
  lc <- literalCount c
  case i < lc && i >= 0 of
    True -> unsafeWriteLiteral c i l
    False -> error ("Clause.writeLiteral index out of bounds: " ++ show (i, l))

forLiterals_ :: (P.PrimMonad m) => Clause m -> Int -> (Int -> L.Literal -> m () -> m ()) -> m ()
forLiterals_ cl ix0 f = do
  lc <- literalCount cl
  go ix0 lc
  where
    go ix lc | ix >= lc = return ()
             | otherwise = do
                 l <- unsafeReadLiteral cl ix
                 f ix l (go (ix + 1) lc)
{-# INLINE forLiterals_ #-}

-- | Swap the literals at the given indices.
swapLiterals :: (P.PrimMonad m) => Clause m -> Int -> Int -> m ()
swapLiterals c ix1 ix2 = do
  nLits <- literalCount c
  case nLits > ix1 && nLits > ix2 of
    False -> error ("Could not swap indices " ++ show ix1 ++ " and " ++ show ix2)
    True -> unsafeSwapLiterals c ix1 ix2

unsafeSwapLiterals :: (P.PrimMonad m) => Clause m -> Int -> Int -> m ()
unsafeSwapLiterals c ix1 ix2 = do
  lit1 <- unsafeReadLiteral c ix1
  lit2 <- unsafeReadLiteral c ix2
  unsafeWriteLiteral c ix1 lit2
  unsafeWriteLiteral c ix2 lit1
{-# INLINE unsafeSwapLiterals #-}

-- | Remove the given 'L.Literal' from the 'Clause' and return the
-- replacement 'L.Literal', if there was one.
removeLiteral :: (P.PrimMonad m) => Clause m -> L.Literal -> m (Maybe L.Literal)
removeLiteral cl lit = do
  lc <- literalCount cl
  go 0 lc
  where
    go ix lc
      | ix >= lc = return Nothing
      | otherwise = do
          l <- unsafeReadLiteral cl ix
          case l == lit of
            False -> go (ix + 1) lc
            True -> do
              case () of
                _  | ix == lc - 1 -> do
                       -- This is the last literal and we have nothing to replace it with
                       writeLiteralCount cl (lc - 1)
                       return Nothing
                   | otherwise -> do
                       newLit <- unsafeReadLiteral cl (lc - 1)
                       unsafeWriteLiteral cl ix newLit
                       writeLiteralCount cl (lc - 1)
                       return (Just newLit)


{- Note [Clause Format]

Clauses are represented as MutableByteArray#.  The fields of the
bytearray are, in order:

 * Double: Clause activity (double index 0)

 * Int16: Number of literals (int16 index 4)

 * Word16: Flags (problem clause, learned clause, or maybe another kind of implied clause) (int16 index 5)

 * Int32[]: The actual literals (starting at int32 index 3)

The flags are:

 * bit 1: 0 if problem, 1 if learned

There are some implications of this format:

 * There can be at most 2^31 clauses

 * No clause can have more than 2^15 literals

These seem like reasonable restrictions

Accessing fields should be relatively simple, but requires a bit of
finesse due to the different sizes of fields and only actually having
array access functions in GHC.Prim.

By convention, the first two literals are the watched literals.  No
clauses should be created with fewer than two literals (to be enforced
later).

-}
