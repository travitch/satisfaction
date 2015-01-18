{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UnboxedTuples #-}
module SAT.Literal (
  -- * Literals
  Literal,
  neg,
  var,
  isNegated,
  toPositiveLiteral,
  toNegativeLiteral,
  invalidLiteral,
  -- * Variables
  Variable,
  mkVariable
  ) where

import qualified GHC.Base as B
import GHC.ST ( ST(..) )

import Control.Monad.ST ( stToIO )

import qualified Data.Array.Unboxed as UA
import qualified Data.Array.IO as IOA
import qualified Data.Array.IO.Internals as IOA
import qualified Data.Array.MArray as MA
import qualified Data.Array.Base as BA
import Data.Bits
import Data.Ix ( Ix )

newtype Variable = MkVariable { varAsInt :: Int }
                 deriving (Eq, Ord, Show, Ix)

newtype Literal = MkLiteral { litAsInt :: Int }
                deriving (Eq, Ord, Show, Ix)

-- | Flip a literal from pos to neg (or neg to pos)
neg :: Literal -> Literal
neg l = MkLiteral (litAsInt l `xor` 1)
{-# INLINE neg #-}

isNegated :: Literal -> Bool
isNegated l = litAsInt l .&. 1 == 0
{-# INLINE isNegated #-}

-- | Find the variable number for the literal
var :: Literal -> Variable
var l = MkVariable (litAsInt l `shiftR` 1)
{-# INLINE var #-}

toPositiveLiteral :: Variable -> Literal
toPositiveLiteral v = MkLiteral (varAsInt v `shiftL` 1)
{-# INLINE toPositiveLiteral #-}

toNegativeLiteral :: Variable -> Literal
toNegativeLiteral v = MkLiteral ((varAsInt v `shiftL` 1) .|. 1)
{-# INLINE toNegativeLiteral #-}

-- | Construct a 'Variable'.
--
-- Note that this representation ('Int') is not guaranteed to be
-- stable.  This is an unsafe function.
mkVariable :: Int -> Variable
mkVariable = MkVariable
{-# INLINE mkVariable #-}

invalidLiteral :: Literal
invalidLiteral = MkLiteral (-1)

deriving instance BA.IArray UA.UArray Literal

instance MA.MArray (BA.STUArray s) Literal (ST s) where
  {-# INLINE getBounds #-}
  getBounds (BA.STUArray l u _ _) = return (l, u)
  {-# INLINE getNumElements #-}
  getNumElements (BA.STUArray _ _ n _) = return n
  {-# INLINE unsafeRead #-}
  unsafeRead (BA.STUArray _ _ _ marr#) (B.I# i#) = ST $ \s1# ->
    case B.readIntArray# marr# i# s1# of
      (# s2#, e# #) -> (# s2#, MkLiteral (B.I# e#) #)
  {-# INLINE unsafeWrite #-}
  unsafeWrite (BA.STUArray _ _ _ marr#) (B.I# i#) (MkLiteral (B.I# e#)) = ST $ \s1# ->
    case B.writeIntArray# marr# i# e# s1# of
      s2# -> (# s2#, () #)

instance MA.MArray IOA.IOUArray Literal IO where
  {-# INLINE getBounds #-}
  getBounds (IOA.IOUArray arr) = stToIO $ BA.getBounds arr
  {-# INLINE getNumElements #-}
  getNumElements (IOA.IOUArray arr) = stToIO $ BA.getNumElements arr
  {-# INLINE unsafeRead #-}
  unsafeRead (IOA.IOUArray arr) i = stToIO $ BA.unsafeRead arr i
  {-# INLINE unsafeWrite #-}
  unsafeWrite (IOA.IOUArray arr) i e = stToIO $ BA.unsafeWrite arr i e
