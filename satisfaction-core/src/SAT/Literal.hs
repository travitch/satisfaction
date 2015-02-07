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
  satisfyLiteral,
  litValue,
  nextLiteral,
  -- * Variables
  Variable,
  firstVariable,
  nextVariable,
  previousVariable,
  -- * History tracking for variables
  State,
  triedNothing,
  triedFalse,
  triedTrue,
  triedBoth,
  -- * Assigned values
  Value,
  liftedTrue,
  liftedFalse,
  unassigned,
  nextValue,
  nextValueState
  ) where

import qualified GHC.Base as B
import qualified GHC.Int as B
import GHC.ST ( ST(..) )

import Control.Applicative
import Control.Monad.ST ( stToIO )

import qualified Data.Array.Unboxed as UA
import qualified Data.Array.IO as IOA
import qualified Data.Array.IO.Internals as IOA
import qualified Data.Array.MArray as MA
import qualified Data.Array.Base as BA
import Data.Bits
import Data.Int ( Int8 )
import Data.Ix ( Ix )
import qualified Data.Ix.Unsafe as UI

newtype Variable = MkVariable { varAsInt :: Int }
                 deriving (Eq, Ord, Show, Ix)

instance UI.Ix0 Variable where
  {-# INLINE unsafeToIndex #-}
  unsafeToIndex = varAsInt

newtype Literal = MkLiteral { litAsInt :: Int }
                deriving (Eq, Ord, Show, Ix)

instance UI.Ix0 Literal where
  {-# INLINE unsafeToIndex #-}
  unsafeToIndex = litAsInt

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
              deriving (Eq, Ord, Show)

liftedTrue :: Value
liftedTrue = MkValue { valueAsInt = 0 }

liftedFalse :: Value
liftedFalse = MkValue { valueAsInt = 1 }

unassigned :: Value
unassigned = MkValue { valueAsInt = 2 }

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

-- | States explicitly track the assignment state of a 'Variable'.
--
-- We want this so that we can avoid large call stacks, instead
-- maintaining state manually in a tail recursive iteration.  Even in
-- Haskell, this will be useful for very large problems.
newtype State = MkState { stateAsInt :: Int8 }
              deriving (Eq, Ord, Show)

triedNothing :: State
triedNothing = MkState { stateAsInt = 0 }

triedTrue :: State
triedTrue = MkState { stateAsInt = 1 }

triedFalse :: State
triedFalse = MkState { stateAsInt = 2 }

triedBoth :: State
triedBoth = MkState { stateAsInt = 3 }

nextValue :: State -> Value
nextValue s = MkValue (stateAsInt s .&. 1)
{-# INLINE nextValue #-}

nextLiteral :: Variable -> State -> Literal
nextLiteral v s = MkLiteral ((varAsInt v `shiftL` 1) .|. fromIntegral (stateAsInt s .&. 1))
{-# INLINE nextLiteral #-}

nextValueState :: Value -> State -> State
nextValueState val st = MkState $ stateAsInt st .|. (1 + fromIntegral (valueAsInt val))
{-# INLINE nextValueState #-}

-- Verbose array instances

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
  unsafeNewArray_ (l, u) = BA.unsafeNewArraySTUArray_ (l, u) BA.wORD_SCALE

instance MA.MArray IOA.IOUArray Literal IO where
  {-# INLINE getBounds #-}
  getBounds (IOA.IOUArray arr) = stToIO $ BA.getBounds arr
  {-# INLINE getNumElements #-}
  getNumElements (IOA.IOUArray arr) = stToIO $ BA.getNumElements arr
  {-# INLINE unsafeRead #-}
  unsafeRead (IOA.IOUArray arr) i = stToIO $ BA.unsafeRead arr i
  {-# INLINE unsafeWrite #-}
  unsafeWrite (IOA.IOUArray arr) i e = stToIO $ BA.unsafeWrite arr i e
  unsafeNewArray_ bounds = stToIO (IOA.IOUArray <$> BA.unsafeNewArray_ bounds)

deriving instance BA.IArray UA.UArray Value

instance MA.MArray (BA.STUArray s) Value (ST s) where
  {-# INLINE getBounds #-}
  getBounds (BA.STUArray l u _ _) = return (l, u)
  {-# INLINE getNumElements #-}
  getNumElements (BA.STUArray _ _ n _) = return n
  {-# INLINE unsafeRead #-}
  unsafeRead (BA.STUArray _ _ _ marr#) (B.I# i#) = ST $ \s1# ->
    case B.readInt8Array# marr# i# s1# of
      (# s2#, e# #) -> (# s2#, MkValue (B.I8# e#) #)
  {-# INLINE unsafeWrite #-}
  unsafeWrite (BA.STUArray _ _ _ marr#) (B.I# i#) (MkValue (B.I8# e#)) = ST $ \s1# ->
    case B.writeInt8Array# marr# i# e# s1# of
      s2# -> (# s2#, () #)
  unsafeNewArray_ (l, u) = BA.unsafeNewArraySTUArray_ (l, u) (\x -> x)

instance MA.MArray IOA.IOUArray Value IO where
  {-# INLINE getBounds #-}
  getBounds (IOA.IOUArray arr) = stToIO $ BA.getBounds arr
  {-# INLINE getNumElements #-}
  getNumElements (IOA.IOUArray arr) = stToIO $ BA.getNumElements arr
  {-# INLINE unsafeRead #-}
  unsafeRead (IOA.IOUArray arr) i = stToIO $ BA.unsafeRead arr i
  {-# INLINE unsafeWrite #-}
  unsafeWrite (IOA.IOUArray arr) i e = stToIO $ BA.unsafeWrite arr i e
  unsafeNewArray_ bounds = stToIO (IOA.IOUArray <$> BA.unsafeNewArray_ bounds)

deriving instance BA.IArray UA.UArray State

instance MA.MArray (BA.STUArray s) State (ST s) where
  {-# INLINE getBounds #-}
  getBounds (BA.STUArray l u _ _) = return (l, u)
  {-# INLINE getNumElements #-}
  getNumElements (BA.STUArray _ _ n _) = return n
  {-# INLINE unsafeRead #-}
  unsafeRead (BA.STUArray _ _ _ marr#) (B.I# i#) = ST $ \s1# ->
    case B.readInt8Array# marr# i# s1# of
      (# s2#, e# #) -> (# s2#, MkState (B.I8# e#) #)
  {-# INLINE unsafeWrite #-}
  unsafeWrite (BA.STUArray _ _ _ marr#) (B.I# i#) (MkState (B.I8# e#)) = ST $ \s1# ->
    case B.writeInt8Array# marr# i# e# s1# of
      s2# -> (# s2#, () #)
  unsafeNewArray_ (l, u) = BA.unsafeNewArraySTUArray_ (l, u) (\x -> x)

instance MA.MArray IOA.IOUArray State IO where
  {-# INLINE getBounds #-}
  getBounds (IOA.IOUArray arr) = stToIO $ BA.getBounds arr
  {-# INLINE getNumElements #-}
  getNumElements (IOA.IOUArray arr) = stToIO $ BA.getNumElements arr
  {-# INLINE unsafeRead #-}
  unsafeRead (IOA.IOUArray arr) i = stToIO $ BA.unsafeRead arr i
  {-# INLINE unsafeWrite #-}
  unsafeWrite (IOA.IOUArray arr) i e = stToIO $ BA.unsafeWrite arr i e
  unsafeNewArray_ bounds = stToIO (IOA.IOUArray <$> BA.unsafeNewArray_ bounds)

{- Note [Next State]

While we are backtracking, we need to pick the next Value to try to
assign to a Variable.  The state is tracked in the eVarStates array
with the values triedNothing (0), triedFalse (1), triedTrue (2), and
triedBoth (3).  We track states explicitly so that they aren't stored
in the stack; this is more compact and easier to resume from when we
freeze state.

Based on these states, we have a simple goal: choose the next state.
Our decisions are easily encoded in a table:

State | Next Value | Next State | Reason
-----------------------------------------
0 | 0 or 1 | 1 or 2 | Doesn't matter which we choose first
1 | 1      | 3      | If we tried false, we want to try true
2 | 0      | 3      | If we tried true, try false next
3 | -      | -      | We tried both, backtrack again

We explicitly check for the last case and then backtrack again if
necessary.  Otherwise, we want a function we can apply to the current
State to get the next Value to try and the next State.  This gets a
bit messy since we need to have computations involving the two
different types, so we end up unwrapping the newtypes here.  This note
works through the cases so that we can be confident it is correct.

The functions we use are:

nextValue(s) = (s ^ 2) & 1
nextState(s, v') = s | (1 << v')

State | nextValue(s)
---------------------
0 | (0 ^ 2) & 1 = 0   (try False first)
1 | (1 ^ 2) & 1 = 1   (tried False, try True next)
2 | (2 ^ 2) & 1 = 0   (tried True, try False next)
3 | N/A, checked separately

State | nextValue(s) | nextState(s, v)
--------------------------------------
0 | 0 | 0 .|. (1 << 0) = 1   (next state is triedFalse)
1 | 1 | 1 .|. (1 << 1) = 3   (next state is triedBoth)
2 | 0 | 2 .|. (1 << 0) = 3   (next state is triedBoth)
3 | N/A

-}
