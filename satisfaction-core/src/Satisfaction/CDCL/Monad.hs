{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-- | These are internal types for the solver
--
-- These types are internal and specific to the CDCL solver.  More
-- reusable types are in the SAT.* namespace.
module Satisfaction.CDCL.Monad (
  Config(..),
  LearningLimit(..),
  Env(..),
  Solver,
  runSolver,
  ask,
  asks,
  liftIO,
  assignVariableValue,
  getDecisionLevel
  ) where

import GHC.IO ( IO(..) )
import GHC.Exts ( RealWorld )

import Control.Applicative
import Control.Monad ( ap )
import qualified Control.Monad.Prim as P
import qualified Data.Foldable as F
import Data.IORef
import Data.Int ( Int8 )
import Data.Ix ( range, rangeSize )
import Prelude

import qualified Data.Array.Heap as H
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

import qualified Satisfaction.CDCL.Clause as C
import qualified Satisfaction.Formula.CNF as CNF
import qualified Satisfaction.Formula.Literal as L
import qualified Satisfaction.Internal.Debug as D

-- | Different ways to specify the (initial) maximum number of learned
-- clauses.  It can be either a ratio of the number of problem clauses
-- or an absolute count.
data LearningLimit = LLRelativeRatio Double
                   | LLAbsolute Int

-- | The configurable parameters of the solver.
--
-- The individual options are documented in
-- 'Satisfaction.Internal.Solver' with the opaque setters exposed to
-- clients.
data Config = Config { cVariableActivityDecayFactor :: Double
                     , cClauseActivityDecayFactor :: Double
                     , cMaxLearnedClauses :: LearningLimit
                     , cMaxLearnedClauseGrowthFactor :: Double
                     , cMaxConflicts :: Int
                     , cMaxConflictGrowthFactor :: Double
                     }

-- | The Reader environment.
--
-- The last variable is an IORef because we may want to add new variables
-- internally later (e.g., for SMT solving).
data Env = Env { eConfig :: Config
               , eClausesWatchingLiteral :: PMA.MArray Solver L.Literal (V.Vector PMA.MArray Solver Int (C.Clause Solver))
                 -- ^ This array is of length @2n@.  Index @i@ is the
                 -- list of clauses (by index) watching literal @i@.
                 -- Index @2i+1@ is the list of clauses watching @~i@.
               , eAssignment :: PUMA.MArray Solver L.Variable L.Value
                 -- ^ The current assignment state
               , eDecisionStack :: V.Vector PUMA.MArray Solver Int L.Literal
                 -- ^ A record of the decisions made
               , eDecisionBoundaries :: V.Vector PUMA.MArray Solver Int Int
                 -- ^ Boundary markers between decision
                 -- levels in the decision stack.
               , eVarLevels :: PUMA.MArray Solver L.Variable Int
                 -- ^ The decision level for each variable.
               , eDecisionReasons :: PMA.MArray Solver L.Variable (Maybe (C.Clause Solver))
                 -- ^ The clause that was the reason for a
                 -- given assertion.  -1 if this was a decision.
               , eProblemClauses :: V.Vector PMA.MArray Solver Int (C.Clause Solver)
                 -- ^ Given problem clauses
               , eLearnedClauses :: V.Vector PMA.MArray Solver Int (C.Clause Solver)
                 -- ^ Learned clause storage
               , eLearnedClauseCount :: P.Ref Solver Int
                 -- ^ The number of learned clauses.
               , ePropagationQueue :: P.Ref Solver Int
                 -- ^ Literals that have been assigned False that we
                 -- need to propagate units for.  This is an index
                 -- into the decision stack.
               , eMaxLearnedClauses :: P.Ref Solver Int
               , eFirstVar :: L.Variable
               , eLastVar :: P.Ref Solver L.Variable
               , eVariableOrder :: H.Heap PUMA.MArray Solver L.Variable
               , eVariableIncrement :: P.Ref Solver Double
               , eVariableActivity :: PUMA.MArray Solver L.Variable Double
               , eClauseIncrement :: P.Ref Solver Double
               , eMaxConflicts :: P.Ref Solver Int
                 -- ^ The maximum number of conflicts to allow before
                 -- restarting.  If this is -1, do not restart.
               , eCurrentConflicts :: P.Ref Solver Int
                 -- ^ The number of conflicts since the last restart

                 -- Overall statistics

               , eTotalConflicts :: P.Ref Solver Int
                 -- ^ The total number of conflicts encountered
               , eRestartCount :: P.Ref Solver Int
                 -- ^ The number of restarts
               , eAtGround :: P.Ref Solver Int
                 -- ^ The number of times we backtracked to the ground decision level
               , eDecisionCount :: P.Ref Solver Int
                 -- ^ The number of decisions made
               , ePropagations :: P.Ref Solver Int
                 -- ^ The number of propagations
               , eLearnedCleanup :: P.Ref Solver Int
                 -- ^ The number of times the learned clause DB was reduced

                 -- Cached storage

               , eSeen :: PUMA.MArray Solver L.Variable Int8
                 -- ^ Variables that have been seen during conflict
                 -- analysis.  This is only used during conflict
                 -- analysis, but is retained globally to avoid having
                 -- to re-allocate it constantly.
               }

-- | Try to assert a literal, returning False if the assertion causes
-- a contradiction.
tryAssertLiteral :: L.Literal -> Maybe (C.Clause Solver) -> Solver Bool
tryAssertLiteral lit reason = do
  e <- ask
  let var = L.var lit
      val = L.satisfyLiteral lit
  val0 <- GA.unsafeReadArray (eAssignment e) var
  case val0 /= L.unassigned && val0 /= val of
    True -> return False
    False -> do
      assignVariableValue var val reason
      V.unsafePush (eDecisionStack e) lit
      return True

-- | Get the current decision level
getDecisionLevel :: Solver Int
getDecisionLevel = do
  bv <- asks eDecisionBoundaries
  V.size bv
{-# INLINE getDecisionLevel #-}

-- | Assign a 'L.Value' to a 'L.Variable'.
--
-- Note that the 'State' is always required to be updated at the same
-- time.
assignVariableValue :: L.Variable -> L.Value -> Maybe (C.Clause Solver) -> Solver ()
assignVariableValue var val reason = do
  e <- ask
  dl <- getDecisionLevel
  liftIO $ D.traceIO ("  [assign] Assigning " ++ show val ++ " to " ++ show var ++ " at " ++ show dl)
  GA.unsafeWriteArray (eAssignment e) var val
  GA.unsafeWriteArray (eVarLevels e) var dl
  GA.unsafeWriteArray (eDecisionReasons e) var reason
{-# INLINE assignVariableValue #-}


-- | A context in which a solver runs.  This is basically a ReaderT IO.
newtype Solver a = S { runS :: Env -> IO a }

-- | Run a solver with an environment set up for a given CNF formula.
runSolver :: Config -> CNF.CNF b -> (Bool -> Solver a) -> IO a
runSolver config cnf comp =
  runS (bootstrapEnv config cnf comp) undefined

bootstrapEnv :: Config -> CNF.CNF b -> (Bool -> Solver a) -> Solver a
bootstrapEnv config cnf comp = do
  let vrange@(lowVar, highVar) = CNF.variableRange cnf
      lrange = (L.toPositiveLiteral lowVar, L.toNegativeLiteral highVar)
      nLits = rangeSize lrange
      nVars = rangeSize vrange
      nClauses = CNF.clauseCount cnf
      maxLearnedClauses =
        case cMaxLearnedClauses config of
          LLAbsolute i -> i
          LLRelativeRatio r -> floor (r * fromIntegral (CNF.clauseCount cnf))
      learnedCap = maxLearnedClauses * 2
  -- There is an assignment for each variable
  assignment <- GA.newArray nVars L.unassigned
  -- Watchlist
  cwl <- GA.newArray_ nLits
  F.forM_ (range lrange) $ \l -> do
    v <- V.new nClauses undefined -- invalid clauses
    GA.unsafeWriteArray cwl l v

  -- We only need the decision stack to be able to hold all of the literals
  decisionStack <- V.new nLits L.invalidLiteral
  decisionBounds <- V.new nLits (-1)
  varLevels <- GA.newArray nVars (-1)
  seen <- GA.newArray nVars 0
  qref <- P.newRef 0
  highVarRef <- P.newRef highVar
  reasons <- GA.newArray nVars Nothing
  pclauses <- V.new (CNF.clauseCount cnf) undefined

  varAct <- GA.newArray nVars 0
  let ordering v1 v2 = do
        v1a <- GA.unsafeReadArray varAct v1
        v2a <- GA.unsafeReadArray varAct v2
        return (v1a > v2a)
  heap <- H.new nVars ordering lowVar
  varInc <- P.newRef 1
  clauseInc <- P.newRef 1
  maxRef <- P.newRef maxLearnedClauses
  initializeVariableOrdering heap lowVar highVar
  lclauses <- V.new learnedCap undefined
  maxConflicts <- P.newRef (cMaxConflicts config)
  curConflicts <- P.newRef 0
  totalConflicts <- P.newRef 0
  restartCount <- P.newRef 0
  groundCount <- P.newRef 0
  props <- P.newRef 0
  decisions <- P.newRef 0
  cleanup <- P.newRef 0
  lccount <- P.newRef 0
  let env = Env { eConfig = config
                , eClausesWatchingLiteral = cwl
                , eAssignment = assignment
                , eDecisionStack = decisionStack
                , eDecisionBoundaries = decisionBounds
                , eDecisionReasons = reasons
                , ePropagationQueue = qref
                , eProblemClauses = pclauses
                , eLearnedClauses = lclauses
                , eLearnedClauseCount = lccount
                , eVarLevels = varLevels
                , eMaxLearnedClauses = maxRef
                , eFirstVar = lowVar
                , eLastVar = highVarRef
                , eVariableOrder = heap
                , eVariableIncrement = varInc
                , eVariableActivity = varAct
                , eClauseIncrement = clauseInc
                , eMaxConflicts = maxConflicts
                , eCurrentConflicts = curConflicts
                , eTotalConflicts = totalConflicts
                , eRestartCount = restartCount
                , eAtGround = groundCount
                , eDecisionCount = decisions
                , ePropagations = props
                , eLearnedCleanup = cleanup
                , eSeen = seen
                }

  liftIO (runS (initializeWatches cnf >>= comp) env)

ask :: Solver Env
ask = S $ \r -> return r
{-# INLINE ask #-}

asks :: (Env -> a) -> Solver a
asks f = S $ \r -> return (f r)
{-# INLINE asks #-}

instance Monad Solver where
  {-# INLINE return #-}
  {-# INLINE (>>) #-}
  {-# INLINE (>>=) #-}
  return x = S $ \_ -> return x
  (>>=) = bindS

bindS :: Solver a -> (a -> Solver b) -> Solver b
bindS m k = S $ \r -> do
  a <- runS m r
  runS (k a) r
{-# INLINE bindS #-}

instance P.PrimMonad Solver where
  type PrimState Solver = RealWorld
  {-# INLINE primitive #-}
  primitive x = S $ \_ -> IO x

instance P.PrimRef Solver where
  type Ref Solver = IORef
  {-# INLINE newRef #-}
  {-# INLINE readRef #-}
  {-# INLINE writeRef #-}
  {-# INLINE modifyRef' #-}
  newRef v = liftIO (newIORef v)
  readRef r = liftIO (readIORef r)
  writeRef r v = liftIO (writeIORef r v)
  modifyRef' r f = liftIO (modifyIORef' r f)

instance Functor Solver where
  fmap f m = S $ \r -> do
    a <- runS m r
    return (f a)

instance Applicative Solver where
  pure = return
  (<*>) = ap

liftIO :: IO a -> Solver a
liftIO a = S $ \_ -> a
{-# INLINE liftIO #-}

-- | Insert all variables into the variable ordering
initializeVariableOrdering :: H.Heap PUMA.MArray Solver L.Variable
                           -> L.Variable
                           -> L.Variable
                           -> Solver ()
initializeVariableOrdering heap lowVar highVar = go lowVar
  where
    go v
      | v > highVar = return ()
      | otherwise = do
          H.unsafeInsert heap v
          initializeVariableOrdering heap (L.nextVariable v) highVar

-- | Initialize the watches.  Each clause starts by watching its first
-- two literals.  Clauses with only one literal are unit clauses,
-- whose literals are automatically inserted into the worklist
--
-- Returns True if there is a trivial contradiction
initializeWatches :: CNF.CNF a -> Solver Bool
initializeWatches cnf = do
  e <- ask
  let clauses = eProblemClauses e
      cwl = eClausesWatchingLiteral e
  AT.foldArrayM (watchFirst cwl clauses) False (CNF.clauseArray cnf)
  where
    -- Empty clauses are discarded.  Clauses with a single literal
    -- assert that literal.  Otherwise, construct an internal problem
    -- clause (which implicitly has two watched literals).
    watchFirst cwl clauses hasContradiction _ix clause = do
      case CNF.clauseLiterals clause of
        [] -> return hasContradiction
        l : [] -> do
          validAssertion <- tryAssertLiteral l Nothing
          return (hasContradiction || not validAssertion)
        lits@(l1 : l2 : _) -> do
          cl <- C.new 0 lits
          V.push clauses cl
          l1w <- GA.readArray cwl l1
          V.push l1w cl
          l2w <- GA.readArray cwl l2
          V.push l2w cl
          return hasContradiction

{- note [Learned Clause Watches]

This is an important but understated part of the minisat algorithm.

Assume that the solver state is at decision level D when it reaches a
conflict.  The conflict analysis function (see
@SAT.Solver.AnalyzeConflict@) constructs an *asserting clause* @LC@
and a backtracking level D'.  The clause is asserting because, after
backtracking to level D', @LC@ is unit.  That is, all but one literal
is False, so that final literal must be assigned such that it is true
(hence, @LC@ asserts that literal).

To maintain the watched literal invariant, we must watch this
asserting literal.  The choice of the other literal to watch is not as
obvious.  It turns out that a literal that was assigned at the second
highest level in @LC@ must be watched.  It turns out that this is also
the level that was backjumped to.

This is critical.  If a literal at a lower level is chosen as the
second watch, the next time the solver backtracks, it could end up in
a state where it is watching an unassigned literal (the former
asserting literal) and a *False* literal.  This violates the watchlist
invariant.

During normal execution with non-learned clauses, watches are
naturally arranged in this way and are safe.  Learned clauses must be
initialized with an appropriate watch that will leave things
consistent, hence the 'watchFirstAtLevel' function.

-}

{- Note [VSIDS]

VSIDS stands for Variable State Independent Decaying Sum.  It is a
heuristic for choosing the variable assignment order during the
search.  The idea is to assign each variable an activity score.
Activity is increased when a variable is involved in a conflict;
variables involved in more conflicts will be resolved sooner.
Ideally, this resolves conflicts earlier in the search.

-}
