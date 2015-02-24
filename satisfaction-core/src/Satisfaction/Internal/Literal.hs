{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UnboxedTuples #-}
-- | This module defines the primitive types used to talk about
-- variables.  See Note [Representation]
module Satisfaction.Internal.Literal (
  -- * Literals
  Literal,
  neg,
  var,
  isNegated,
  toPositiveLiteral,
  toNegativeLiteral,
  invalidLiteral,
  satisfyLiteral,
  litValue,
  -- * Variables
  Variable,
  firstVariable,
  nextVariable,
  previousVariable,
  -- * Assigned values
  Value,
  liftedTrue,
  liftedFalse,
  unassigned,
  isUnassigned
  ) where

import GHC.Int

import Data.Bits
import Data.Ix ( Ix )
import Data.Ix.Zero
import Data.Unbox

newtype Variable = MkVariable { varAsInt :: Int }
                 deriving (Eq, Ord, Show, Ix, Unbox)

instance IxZero Variable where
  {-# INLINE toZeroIndex #-}
  {-# INLINE fromZeroIndex #-}
  toZeroIndex = varAsInt
  fromZeroIndex = MkVariable

newtype Literal = MkLiteral { litAsInt :: Int }
                deriving (Eq, Ord, Show, Ix, Unbox)

instance IxZero Literal where
  {-# INLINE toZeroIndex #-}
  {-# INLINE fromZeroIndex #-}
  toZeroIndex = litAsInt
  fromZeroIndex = MkLiteral

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

-- | The first variable in the sequence
firstVariable :: Variable
firstVariable = MkVariable 0

-- | Get the next variable in the sequence (starting from
-- 'firstVariable')
nextVariable :: Variable -> Variable
nextVariable = MkVariable . (+1) . varAsInt

-- | Try to get the previous variable, if any.
previousVariable :: Variable -> Maybe Variable
previousVariable (MkVariable vnum)
  | vnum <= 0 = Nothing
  | otherwise = Just (MkVariable (vnum - 1))
{-# INLINE previousVariable #-}

invalidLiteral :: Literal
invalidLiteral = MkLiteral (-1)

-- | These are lifted booleans: LTrue, LFalse, and unassigned
--
-- We waste a few bits here, but doing fancy bit packing would
-- probably be an overall loss.  Besides, the space for the assignment
-- isn't really a bottleneck.
newtype Value = MkValue { valueAsInt :: Int8 }
              deriving (Eq, Ord, Show, Unbox)

liftedTrue :: Value
liftedTrue = MkValue { valueAsInt = 0 }

liftedFalse :: Value
liftedFalse = MkValue { valueAsInt = 1 }

unassigned :: Value
unassigned = MkValue { valueAsInt = 2 }

-- | A predicate to see if a value is unassigned.  We use this instead
-- of an equality check because unassigned can actually work out to be
-- 2 or 3 due to a quirk in litValue or satisfyLiteral.
isUnassigned :: Value -> Bool
isUnassigned v = v >= unassigned
{-# INLINE isUnassigned #-}

-- | Compute the 'Value' that satisfies the given 'Literal'
--
-- If the lit is negated, 1.  Otherwise, 0
satisfyLiteral :: Literal -> Value
satisfyLiteral l = MkValue { valueAsInt = fromIntegral (litAsInt l .&. 1) }
{-# INLINE satisfyLiteral #-}

-- | Given a 'Literal' and the value assigned to its underlying
-- 'Variable', determine the resulting 'Value'
litValue :: Literal -> Value -> Value
litValue l v = MkValue { valueAsInt = valueAsInt v `xor` fromIntegral (litAsInt l .&. 1) }
{-# INLINE litValue #-}

{- Note [Representation]

Variables are (newtypes of) Ints from [0..N].

The positive literal of variable @n@ is @2n@.  The negative literal of
variable @n@ is @2n+1@.

Assigned values are lifted booleans.  True is represented as (byte)
zero.  False is one.  Unassigned (bottom) is 2.  This representation
is odd, but it makes some operations very convenient (see above).

-}
