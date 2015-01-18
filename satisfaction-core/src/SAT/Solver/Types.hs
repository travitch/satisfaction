{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UnboxedTuples #-}
-- | These are internal types for the solver
--
-- These types are internal and specific to the CDCL solver.  More
-- reusable types are in the SAT.* namespace.
module SAT.Solver.Types (
  Value,
  liftedTrue,
  liftedFalse,
  unassigned,
  Assignment,
  -- * History tracking for variables
  State,
  nothingTried,
  onlyFalseTried,
  onlyTrueTried,
  bothTried,
  -- * Solver Monad
  Solver,
  runSolver,
  ask,
  asks,
  liftIO,
  takeWork
  ) where

import qualified GHC.Base as B
import qualified GHC.Int as B
import GHC.ST ( ST(..) )

import Control.Applicative
import Control.Monad ( ap )
import Control.Monad.ST ( stToIO )
import qualified Data.Array.Unboxed as UA
import qualified Data.Array.IO as IOA
import qualified Data.Array.IO.Internals as IOA
import qualified Data.Array.MArray as MA
import qualified Data.Array.Base as BA
import Data.Int ( Int8 )
import Data.IORef
import Data.Sequence ( Seq )
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import qualified Data.Array.Traverse as AT
import qualified SAT.CNF as C
import qualified SAT.Literal as L

-- | These are lifted booleans: LTrue, LFalse, and unassigned
--
-- We waste a few bits here, but doing fancy bit packing would
-- probably be an overall loss.  Besides, the space for the assignment
-- isn't really a bottleneck.
newtype Value = MkValue { valueAsInt :: Int8 }
              deriving (Eq, Ord, Show)

liftedTrue :: Value
liftedTrue = MkValue { valueAsInt = 1 }

liftedFalse :: Value
liftedFalse = MkValue { valueAsInt = 0 }

unassigned :: Value
unassigned = MkValue { valueAsInt = -1 }



-- | An assignment of values to variables.  This is of length @n@
-- (i.e., one entry per variable).  1 is True, 0 is False, and -1 is
-- unassigned.
type Assignment = IOA.IOUArray L.Variable Value

type Worklist = Seq L.Literal

emptyWorklist :: Worklist
emptyWorklist = Seq.empty

type ClauseNumber = Int

-- | Our simple watchlist implementing two-watched literals.
--
-- The invariant we maintain is that all watched literals are either
-- assigned true or are unassigned.  If a literal becomes false, all
-- clauses watching it must be updated to watch another literal.  If
-- no additional literal can be found, make the other watched literal
-- true.  If a conflict is found, backtrack.
--
-- Singleton clauses will be processed immediately and have sentinel
-- values in this structure.
data Watchlist =
  Watchlist { wlVarWatches :: IOA.IOArray L.Literal (Seq ClauseNumber)
              -- ^ This array is of length @2n@.  Index @i@ is the
              -- list of clauses (by index) watching literal @i@.
              -- Index @2i+1@ is the list of clauses watching @~i@.
            , wlClauseWatches :: IOA.IOUArray ClauseNumber L.Literal
              -- ^ The array is of length @2c@ where @c@ is the number
              -- of clauses.  Index @2i@ is the first literal being
              -- watched for clause @i@.  Index @2i+1@ is the second
              -- literal being watched for clause @i@.
            }

-- | States explicitly track the assignment state of a 'Variable'.
--
-- We want this so that we can avoid large call stacks, instead
-- maintaining state manually in a tail recursive iteration.  Even in
-- Haskell, this will be useful for very large problems.
newtype State = MkState { stateAsInt :: Int8 }
              deriving (Eq, Ord, Show)

nothingTried :: State
nothingTried = MkState { stateAsInt = 0 }

onlyFalseTried :: State
onlyFalseTried = MkState { stateAsInt = 1 }

onlyTrueTried :: State
onlyTrueTried = MkState { stateAsInt = 2 }

bothTried :: State
bothTried = MkState { stateAsInt = 3 }

newtype States = States { unStates :: IOA.IOUArray L.Variable State }

-- The solver Monad, which is just an opaque IO Monad with a Reader
-- environment



-- | The Reader environment.  We quantify away the type parameter to
-- the formula because we never need to look at its reverse mapping.
data Env = forall a . Env { eWatchlist :: Watchlist
                          , eAssignment :: Assignment
                          , eVarStates :: States
                          , eWorklist :: IORef Worklist
                          , eCNF :: C.CNF a
                          }


-- | A context in which a solver runs.  This is basically a ReaderT IO.
newtype Solver a = S { runS :: Env -> IO a }

-- | Run a solver with an environment set up for a given CNF formula.
runSolver :: C.CNF b -> Solver a -> IO a
runSolver cnf comp = do
  let lrange = literalRange cnf
      vrange = variableRange cnf
      nClauses = C.clauseCount cnf
  -- There is an assignment for each variable
  assignment <- MA.newArray vrange unassigned
  watchlist <- Watchlist <$> MA.newArray lrange Seq.empty <*> MA.newArray (0, 2 * nClauses - 1) L.invalidLiteral
  -- We get an initial worklist composed of all of the unit clauses
  wl0 <- initializeWatches cnf watchlist
  states <- States <$> MA.newArray vrange nothingTried
  work <- newIORef wl0
  let env = Env { eCNF = cnf
                , eAssignment = assignment
                , eVarStates = states
                , eWorklist = work
                , eWatchlist = watchlist
                }

  runS comp env

{-# INLINE ask #-}
ask :: Solver Env
ask = S $ \r -> return r

{-# INLINE asks #-}
asks :: (Env -> a) -> Solver a
asks f = S $ \r -> return (f r)

instance Monad Solver where
  {-# INLINE return #-}
  {-# INLINE (>>) #-}
  {-# INLINE (>>=) #-}
  return x = S $ \_ -> return x
  (>>=) = bindS

{-# INLINE bindS #-}
bindS :: Solver a -> (a -> Solver b) -> Solver b
bindS m k = S $ \r -> do
  a <- runS m r
  runS (k a) r

instance Functor Solver where
  fmap f m = S $ \r -> do
    a <- runS m r
    return (f a)

instance Applicative Solver where
  pure = return
  (<*>) = ap

{-# INLINE liftIO #-}
liftIO :: IO a -> Solver a
liftIO a = S $ \_ -> a

-- | Initialize the watches.  Each clause starts by watching its first
-- two literals.  Clauses with only one literal are not processed
-- here.  They will be taken care of next.
initializeWatches :: C.CNF a -> Watchlist -> IO Worklist
initializeWatches cnf wl =
  AT.foldArrayM watchFirst emptyWorklist (C.clauses cnf)
  where
    watchFirst work ix clause = do
      case C.clauseLiterals clause of
        l1 : l2 : _ -> do
          MA.writeArray (wlClauseWatches wl) (2 * ix) l1
          MA.writeArray (wlClauseWatches wl) (2 * ix + 1) l2
          let varWatches = wlVarWatches wl
          l1w <- MA.readArray varWatches l1
          MA.writeArray varWatches l1 (l1w Seq.|> ix)
          l2w <- MA.readArray varWatches l2
          MA.writeArray varWatches l2 (l2w Seq.|> ix)
          return work
        l : [] -> return (work Seq.|> l)
        [] -> return work


takeWork :: Solver (Maybe L.Literal)
takeWork = do
  wlref <- asks eWorklist
  wl <- liftIO $ readIORef wlref
  case Seq.viewl wl of
    Seq.EmptyL -> return Nothing
    work Seq.:< rest -> do
      liftIO $ writeIORef wlref rest
      return (Just work)
{-# INLINE takeWork #-}





-- Basic helpers

-- | It is not possible to construct a 'CNF' instance with no clauses
-- (or an empty clause), so there is always at least one literal and
-- this is total.
findRangeWith :: (Ord b) => (L.Literal -> b) -> C.CNF a -> (b, b)
findRangeWith f cnf = (S.findMin s, S.findMax s)
  where
    s = S.fromList [ f l | c <- C.clauseList cnf, l <- C.clauseLiterals c ]

literalRange :: C.CNF a -> (L.Literal, L.Literal)
literalRange = findRangeWith id

variableRange :: C.CNF a -> (L.Variable, L.Variable)
variableRange = findRangeWith L.var




-- Inane Array instances

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

instance MA.MArray IOA.IOUArray Value IO where
  {-# INLINE getBounds #-}
  getBounds (IOA.IOUArray arr) = stToIO $ BA.getBounds arr
  {-# INLINE getNumElements #-}
  getNumElements (IOA.IOUArray arr) = stToIO $ BA.getNumElements arr
  {-# INLINE unsafeRead #-}
  unsafeRead (IOA.IOUArray arr) i = stToIO $ BA.unsafeRead arr i
  {-# INLINE unsafeWrite #-}
  unsafeWrite (IOA.IOUArray arr) i e = stToIO $ BA.unsafeWrite arr i e

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

instance MA.MArray IOA.IOUArray State IO where
  {-# INLINE getBounds #-}
  getBounds (IOA.IOUArray arr) = stToIO $ BA.getBounds arr
  {-# INLINE getNumElements #-}
  getNumElements (IOA.IOUArray arr) = stToIO $ BA.getNumElements arr
  {-# INLINE unsafeRead #-}
  unsafeRead (IOA.IOUArray arr) i = stToIO $ BA.unsafeRead arr i
  {-# INLINE unsafeWrite #-}
  unsafeWrite (IOA.IOUArray arr) i e = stToIO $ BA.unsafeWrite arr i e


{-

Draft of CPS monad support

data SATError = SATError

newtype Solver2 a =
  S2 { runS2 :: forall r . (a -> Env -> IO (Either SATError r)) -> (Env -> IO (Either SATError r)) }

instance Monad Solver2 where
  {-# INLINE return #-}
  {-# INLINE (>>) #-}
  {-# INLINE (>>=) #-}
  return x = S2 ($x)
  (>>=) = bindSolver

{-# INLINE bindSolver #-}
bindSolver :: Solver2 a -> (a -> Solver2 b) -> Solver2 b
bindSolver m f = S2 $ \k -> runS2 m (\a -> runS2 (f a) k)

instance Functor Solver2 where
  fmap f m = S2 $ \k -> runS2 m (k . f)

instance Applicative Solver2 where
  pure = return
  (<*>) = ap

liftIO2 :: IO a -> Solver2 a
liftIO2 a = S2 $ \k r -> a >>= \x -> k x r

ask2 :: Solver2 Env
ask2 = S2 $ \k r -> return r >>= \x -> k x r

-}
