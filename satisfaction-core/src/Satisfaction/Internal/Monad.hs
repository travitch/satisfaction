{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-- | These are internal types for the solver
--
-- These types are internal and specific to the CDCL solver.  More
-- reusable types are in the SAT.* namespace.
module Satisfaction.Internal.Monad (
  Config(..),
  Statistics(..),
  LearningLimit(..),
  Env(..),
  Solver,
  runSolver,
  ask,
  asks,
  liftIO,
  ClauseRef,
  noClause,
  assertLiteral,
  learnClause,
  undoUntil,
  withNextDecidedLiteral,
  getDecisionLevel,
  incrementDecisionLevel,
  literalValue,
  clauseAt,
  bumpVariableActivity,
  decayVariableActivity,
  bumpClauseActivity,
  decayClauseActivity,
  restartWith,
  extractStatistics,
  extractAssignment
  ) where

import GHC.IO ( IO(..) )
import GHC.Exts ( RealWorld )

import Control.Applicative
import Control.Monad ( ap, replicateM_ )
import qualified Control.Monad.Prim as P
import qualified Data.Foldable as F
import Data.IORef
import Data.Int ( Int8 )
import Data.Ix ( range, rangeSize )
import Prelude

import qualified Data.Array.Dynamic as DA
import qualified Data.Array.Heap as H
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Prim.Unboxed as PUA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified Data.Ref.Prim as P

import qualified Satisfaction.CNF as C
import qualified Satisfaction.Internal.Literal as L
import qualified Satisfaction.Internal.Debug as D

-- | The maximum activity value allowed before all activities are
-- normalized.
activityCap :: Double
activityCap = 1e100

-- | A semi-opaque reference to a clause
type ClauseRef = Int

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
               , eClausesWatchingLiteral :: PMA.MArray Solver L.Literal (V.Vector PUMA.MArray Solver ClauseRef)
                 -- ^ This array is of length @2n@.  Index @i@ is the
                 -- list of clauses (by index) watching literal @i@.
                 -- Index @2i+1@ is the list of clauses watching @~i@.
               , eWatchedLiterals :: DA.DArray PUMA.MArray Solver ClauseRef L.Literal
                 -- ^ The array is of length @2c@ where @c@ is the number
                 -- of clauses.  Index @2i@ is the first literal being
                 -- watched for clause @i@.  Index @2i+1@ is the second
                 -- literal being watched for clause @i@.
               , eAssignment :: PUMA.MArray Solver L.Variable L.Value
                 -- ^ The current assignment state
               , eDecisionStack :: V.Vector PUMA.MArray Solver L.Literal
                 -- ^ A record of the decisions made
               , eDecisionBoundaries :: V.Vector PUMA.MArray Solver Int
                 -- ^ Boundary markers between decision
                 -- levels in the decision stack.
               , eVarLevels :: PUMA.MArray Solver L.Variable Int
                 -- ^ The decision level for each variable.
               , eDecisionReasons :: PUMA.MArray Solver L.Variable ClauseRef
                 -- ^ The clause that was the reason for a
                 -- given assertion.  -1 if this was a decision.
               , eProblemClauses :: PMA.MArray Solver ClauseRef C.Clause
                 -- ^ Given problem clauses
               , eLearnedClauses :: DA.DArray PMA.MArray Solver ClauseRef C.Clause
                 -- ^ Learned clause storage
               , eLearnedClauseCount :: P.Ref Solver Int
                 -- ^ The number of learned clauses.
               , eClauseRefPool :: H.Heap PUMA.MArray Solver ClauseRef
                 -- ^ Available clause refs
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
               , eClauseActivity :: DA.DArray PUMA.MArray Solver ClauseRef Double
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

-- | Solver statistics
data Statistics =
  Statistics { sTotalConflicts :: Int
             , sRestartCount :: Int
             , sGroundLevels :: Int
             , sDecisionCount :: Int
             , sPropagations :: Int
             , sLearnedCleanup :: Int
             }
  deriving (Show)

-- | Read the current statistics out of the state
extractStatistics :: Solver Statistics
extractStatistics = do
  e <- ask
  totalConflicts <- P.readRef (eTotalConflicts e)
  curConflicts <- P.readRef (eCurrentConflicts e)
  restartCount <- P.readRef (eRestartCount e)
  groundLevels <- P.readRef (eAtGround e)
  decisionCount <- P.readRef (eDecisionCount e)
  props <- P.readRef (ePropagations e)
  cleaned <- P.readRef (eLearnedCleanup e)
  return Statistics { sTotalConflicts = totalConflicts + curConflicts
                    , sRestartCount = restartCount
                    , sGroundLevels = groundLevels
                    , sDecisionCount = decisionCount
                    , sPropagations = props
                    , sLearnedCleanup = cleaned
                    }

-- | Look up the clause corresponding to a ClauseRef.
--
-- This is slightly tricky because the clause could either be a
-- problem clause or a learned clause, and they are stored in separate
-- places.
clauseAt :: ClauseRef -> Solver C.Clause
clauseAt clauseRef = do
  e <- ask
  nProblemClauses <- GA.size (eProblemClauses e)
  case clauseRef < nProblemClauses of
    True -> GA.unsafeReadArray (eProblemClauses e) clauseRef
    False -> do
      let cr' = clauseRef - nProblemClauses
      GA.unsafeReadArray (eLearnedClauses e) cr'
{-# INLINE clauseAt #-}

-- | If we have passed the conflict threshold, restart by calling
-- @kRestart@.  Otherwise, continue searching.
--
-- If the number of restarts overflows an Int, just set it to -1.
restartWith :: Solver a -> Solver a -> Solver a
restartWith kRestart kSearch = do
  e <- ask
  curConflicts <- P.readRef (eCurrentConflicts e)
  maxConflicts <- P.readRef (eMaxConflicts e)
  case curConflicts < maxConflicts || maxConflicts == -1 of
    True -> kSearch
    False -> do
      let conf = eConfig e
          nextGrowth = fromIntegral maxConflicts * cMaxConflictGrowthFactor conf
      P.modifyRef' (eTotalConflicts e) (+curConflicts)
      P.writeRef (eCurrentConflicts e) 0
      P.writeRef (eMaxConflicts e) (max (floor nextGrowth) (-1))
      P.modifyRef' (eRestartCount e) (+1)
      maxLearned <- P.readRef (eMaxLearnedClauses e)
      let nextMaxLearned = fromIntegral maxLearned * cMaxLearnedClauseGrowthFactor conf
      P.writeRef (eMaxLearnedClauses e) (floor nextMaxLearned)
      undoUntil 0
      kRestart

-- | Learn a clause and assert its asserting literal.
--
-- The asserting literal is asserted here.
--
-- If the clause is a singleton, this function simply asserts it.  The
-- decision level should be *ground* if the given clause is a
-- singleton, but this function does not check or enforce that.  The
-- clause learning algorithm should have instructed the backtracking
-- function to backjump appropriately.
--
-- Otherwise, this function simply adds the clause to the list of
-- clauses and sets appropriate watches.  The asserting literal, which
-- is assumed to be the first literal, is watched.
-- 'watchFirstAtLevel' chooses the other literal to watch.
--
-- Note that we cannot enforce that learned clause limit here.  We
-- need to at least assert the asserting literal from this clause, but
-- if we do that, we need to have a real clause as its reason.  We
-- cannot say it was a ground literal, since that would mean we could
-- never undo the assignment.  We could, in theory, add a sentinel
-- value that says "this was an asserted literal, but there was no
-- room for its clause", but that is somewhat complicated.  It would
-- also ruin future clause learning involving this literal.  Instead,
-- we'll treat the maximum number of learned clauses as a soft limit
-- and enforce it later (after conflict resolution).
learnClause :: Int -> L.Literal -> C.Clause -> Solver ()
learnClause btLevel l c = do
  e <- ask
  dl <- getDecisionLevel
  liftIO $ D.traceIO ("[lc] Learning clause and asserting " ++ show l ++ " at dl " ++ show dl)
  case C.clauseLiterals c of
    [] -> return ()
    _:[] -> assertLiteral l noClause
    l1:rest@(_:_) -> do
      P.modifyRef' (eLearnedClauseCount e) (+1)
      cref <- allocateClauseRef
      liftIO $ D.traceIO ("  [lc] Clause ref allocated: " ++ show cref)
      nProblemClauses <- GA.size (eProblemClauses e)
      let ix = cref - nProblemClauses
      GA.unsafeWriteArray (eLearnedClauses e) ix c
      setFirstWatch cref l1
      lw1 <- GA.unsafeReadArray (eClausesWatchingLiteral e) l1
      V.push lw1 cref
      watchFirstAtLevel btLevel cref rest
      assertLiteral l cref

-- | Return an unused 'ClauseRef', allocating space for a new one if
-- necessary.  If space must be allocated, this function also extends
-- 'eWatchedLiterals' so that there is sufficient space in the
-- watchlist.
allocateClauseRef :: Solver ClauseRef
allocateClauseRef = do
  e <- ask
  mref <- H.takeMin (eClauseRefPool e)
  nProblemClauses <- GA.size (eProblemClauses e)
  case mref of
    Just ref -> return (ref + nProblemClauses)
    Nothing -> do
      sz0 <- GA.size (eLearnedClauses e)
      let sz1 = sz0 * 2
      DA.grow (eLearnedClauses e) sz1
      DA.grow (eClauseActivity e) sz1
      DA.grow (eWatchedLiterals e) ((nProblemClauses + sz1) * 2)
      F.forM_ [(sz0 + 1) .. (sz1 - 1)] $ \cref -> do
        H.insert (eClauseRefPool e) cref
      return (sz0 + nProblemClauses)

-- | Set the first watch for the given 'ClauseRef' to the named 'L.Literal'
setFirstWatch :: ClauseRef -> L.Literal -> Solver ()
setFirstWatch cref l = do
  e <- ask
  GA.unsafeWriteArray (eWatchedLiterals e) (cref * 2) l
{-# INLINE setFirstWatch #-}

-- | Set the second watch for the given 'ClauseRef' to the named 'L.Literal'
setSecondWatch :: ClauseRef -> L.Literal -> Solver ()
setSecondWatch cref l = do
  e <- ask
  GA.unsafeWriteArray (eWatchedLiterals e) (cref * 2 + 1) l
{-# INLINE setSecondWatch #-}

-- | Choose the first literal from the list that was assigned at the
-- given @btLevel@ to watch, and set up watches.  See Note [Learned
-- Clause Watches] for details.
watchFirstAtLevel :: Int -> ClauseRef -> [L.Literal] -> Solver ()
watchFirstAtLevel btLevel cref lits = go lits
  where
    go [] = error "impossible: No matching literals at watchFirstAtLevel"
    go (l:rest) = do
      e <- ask
      lv <- GA.unsafeReadArray (eVarLevels e) (L.var l)
      case lv == btLevel of
        False -> go rest
        True -> do
          setSecondWatch cref l
          lw2 <- GA.unsafeReadArray (eClausesWatchingLiteral e) l
          V.push lw2 cref

-- | Determine the value of the given 'L.Literal'
--
-- This looks at the assignment of the underlying 'L.Variable' and
-- corrects it for the polarity of the literal.
literalValue :: L.Literal -> Solver L.Value
literalValue l = do
  assignments <- asks eAssignment
  val <- GA.unsafeReadArray assignments (L.var l)
  return $! L.litValue l val
{-# INLINE literalValue #-}

-- | Undo the most recent decision, along with the associated metadata.
undoLastDecision :: Solver ()
undoLastDecision =
  withLastDecision $ \lastLit -> do
    liftIO $ D.traceIO ("  Undoing " ++ show lastLit)
    decisions <- asks eDecisionStack
    assignVariableValue (L.var lastLit) L.unassigned noClause
    resetVariable (L.var lastLit)
    e <- ask
    H.insert (eVariableOrder e) (L.var lastLit)
    V.pop decisions 1
{-# INLINE undoLastDecision #-}

-- | Undo assignments until the given decision level.  This is for use
-- in non-chronological backjumping.
undoUntil :: Int -> Solver ()
undoUntil targetDl = do
  dl <- getDecisionLevel
  case dl > targetDl of
    False -> return ()
    True -> do
      e <- ask
      nAssignments <- V.size (eDecisionStack e)
      dlBoundary <- V.unsafeReadVector (eDecisionBoundaries e) targetDl
      replicateM_ (nAssignments - dlBoundary) undoLastDecision
      P.writeRef (ePropagationQueue e) dlBoundary
      nBounds <- V.size (eDecisionBoundaries e)
      V.pop (eDecisionBoundaries e) (nBounds - targetDl)

-- | Looks up the last decision made and calls the given continuation with it.
--
-- The function doesn't do anything else, so undoing the last decision
-- is safe.
withLastDecision :: (L.Literal -> Solver a) -> Solver a
withLastDecision k = do
  e <- ask
  nDecisions <- V.size (eDecisionStack e)
  lastLit <- V.unsafeReadVector (eDecisionStack e) (nDecisions - 1)
  k lastLit
{-# INLINE withLastDecision #-}

-- | Find the next 'Variable' to assign a value to, implicitly
-- encoding that as a 'Literal'.
--
-- If there are no more variables to assign, extract a solution with
-- the given continuation.
withNextDecidedLiteral :: Solver a -- ^ Continue into the done state (i.e., extract a solution)
                       -> (L.Literal -> Solver a) -- ^ Continue with selected 'Literal'
                       -> Solver a
withNextDecidedLiteral kDone kLit = go
  where
    go = do
      e <- ask
      mvar <- H.takeMin (eVariableOrder e)
      case mvar of
        Nothing -> kDone
        Just var -> do
          val <- GA.unsafeReadArray (eAssignment e) var
          case L.isUnassigned val of
            True -> do
              P.modifyRef' (eDecisionCount e) (+1)
              kLit (L.toPositiveLiteral var)
            False -> go
{-# INLINE withNextDecidedLiteral #-}


-- | Assert a literal.
--
-- This function assumes (but does not check) that the assertion does
-- not cause a conflict.  If it could, call 'tryAssertLiteral'
-- instead.
assertLiteral :: L.Literal -> ClauseRef -> Solver ()
assertLiteral lit clNum = do
  e <- ask
  let var = L.var lit
      val = L.satisfyLiteral lit
  assignVariableValue var val clNum
  V.unsafePush (eDecisionStack e) lit
{-# INLINE assertLiteral #-}

-- | Try to assert a literal, returning False if the assertion causes
-- a contradiction.
tryAssertLiteral :: L.Literal -> ClauseRef -> Solver Bool
tryAssertLiteral lit clNum = do
  e <- ask
  let var = L.var lit
      val = L.satisfyLiteral lit
  val0 <- GA.unsafeReadArray (eAssignment e) var
  case val0 /= L.unassigned && val0 /= val of
    True -> return False
    False -> do
      assignVariableValue var val clNum
      V.unsafePush (eDecisionStack e) lit
      return True

-- | Get the current decision level
getDecisionLevel :: Solver Int
getDecisionLevel = do
  bv <- asks eDecisionBoundaries
  V.size bv
{-# INLINE getDecisionLevel #-}

-- | Increment the current decision level
--
-- The decision level is implicit, and represented as the length of
-- the 'eDecisionBoundaries' list.  This function saves the current
-- size of the decision stack as the new boundary, which increments
-- the decision level.
incrementDecisionLevel :: Solver ()
incrementDecisionLevel = do
  e <- ask
  dl <- V.size (eDecisionStack e)
  V.unsafePush (eDecisionBoundaries e) dl
  level <- getDecisionLevel
  liftIO $ D.traceIO ("[idl] At decision level " ++ show level ++ ", which starts at index " ++ show dl)

-- | Assign a 'L.Value' to a 'L.Variable'.
--
-- Note that the 'State' is always required to be updated at the same
-- time.
assignVariableValue :: L.Variable -> L.Value -> ClauseRef -> Solver ()
assignVariableValue var val clNum = do
  e <- ask
  dl <- getDecisionLevel
  liftIO $ D.traceIO ("  [assign] Assigning " ++ show val ++ " to " ++ show var ++ " at " ++ show dl)
  GA.unsafeWriteArray (eAssignment e) var val
  GA.unsafeWriteArray (eVarLevels e) var dl
  GA.unsafeWriteArray (eDecisionReasons e) var clNum
{-# INLINE assignVariableValue #-}

resetVariable :: L.Variable -> Solver ()
resetVariable var = do
  e <- ask
  liftIO $ D.traceIO ("[reset] Setting the state of " ++ show var ++ " to triedNothing")
  GA.unsafeWriteArray (eAssignment e) var L.unassigned
  GA.unsafeWriteArray (eVarLevels e) var (-1)
  GA.unsafeWriteArray (eDecisionReasons e) var noClause
{-# INLINE resetVariable #-}

-- | Extract the current assignment as a pure value.
--
-- This does not ensure that the assignment is complete (i.e., there
-- could be unassigned values).
extractAssignment :: Solver (PUA.Array L.Variable L.Value)
extractAssignment = do
  a <- asks eAssignment
  PUMA.freeze a

-- | Implicitly decay variable activities by *increasing* the variable
-- activity increment.
decayVariableActivity :: Solver ()
decayVariableActivity = do
  e <- ask
  let decayFactor = cVariableActivityDecayFactor (eConfig e)
  liftIO $ modifyIORef' (eVariableIncrement e) (* (1 / decayFactor))

-- | Bump the activity for a 'L.Variable' by the current increment
-- amount.
--
-- This function normalizes all of the activities if they get too
-- large.  See Note [VSIDS]
bumpVariableActivity :: L.Variable -> Solver ()
bumpVariableActivity var = do
  e <- ask
  amount <- P.readRef (eVariableIncrement e)
  act0 <- GA.unsafeReadArray (eVariableActivity e) var
  let act1 = act0 + amount
  GA.unsafeWriteArray (eVariableActivity e) var act1
  case act1 > activityCap of
    False -> return ()
    True -> do
      let arr = eVariableActivity e
          factor = 1 / activityCap
      AT.forMArray_ arr $ \ix elt -> do
        GA.unsafeWriteArray arr ix (elt * factor)
      P.modifyRef' (eVariableIncrement e) (* factor)
  H.unsafeUpdate (eVariableOrder e) var

-- | Decay existing clause activities implicitly by *increasing* the
-- clause increment value
decayClauseActivity :: Solver ()
decayClauseActivity = do
  e <- ask
  let decayFactor = cClauseActivityDecayFactor (eConfig e)
  liftIO $ modifyIORef' (eClauseIncrement e) (* (1 / decayFactor))

-- | Bump the activity of a learned clause.
--
-- Calling this function on a problem (i.e., non-learned) clause is
-- safe and is a no-op
bumpClauseActivity :: ClauseRef -> Solver ()
bumpClauseActivity cref = do
  e <- ask
  nProblemClauses <- GA.size (eProblemClauses e)
  case cref < nProblemClauses of
    True -> return ()
    False -> do
      let cref' = cref - nProblemClauses
      amount <- P.readRef (eClauseIncrement e)
      act0 <- GA.unsafeReadArray (eClauseActivity e) cref'
      let act1 = act0 + amount
      GA.unsafeWriteArray (eClauseActivity e) cref' act1
      case act1 > activityCap of
        False -> return ()
        True -> do
          let arr = eClauseActivity e
              factor = 1 / activityCap
          AT.forMArray_ arr $ \ix elt -> do
            GA.unsafeWriteArray arr ix (elt * factor)
          P.modifyRef' (eClauseIncrement e) (* factor)

-- | A context in which a solver runs.  This is basically a ReaderT IO.
newtype Solver a = S { runS :: Env -> IO a }

-- | Run a solver with an environment set up for a given CNF formula.
runSolver :: Config -> C.CNF b -> (Bool -> Solver a) -> IO a
runSolver config cnf comp =
  runS (bootstrapEnv config cnf comp) undefined

bootstrapEnv :: Config -> C.CNF b -> (Bool -> Solver a) -> Solver a
bootstrapEnv config cnf comp = do
  let vrange@(lowVar, highVar) = C.variableRange cnf
      lrange = (L.toPositiveLiteral lowVar, L.toNegativeLiteral highVar)
      nLits = rangeSize lrange
      nVars = rangeSize vrange
      nClauses = C.clauseCount cnf
      maxLearnedClauses =
        case cMaxLearnedClauses config of
          LLAbsolute i -> i
          LLRelativeRatio r -> floor (r * fromIntegral (C.clauseCount cnf))
      learnedCap = maxLearnedClauses * 2
  -- There is an assignment for each variable
  assignment <- GA.newArray nVars L.unassigned
  -- Watchlist
  cwl <- GA.newArray_ nLits
  F.forM_ (range lrange) $ \l -> do
    v <- V.new nClauses noClause
    GA.unsafeWriteArray cwl l v
  wl <- GA.newArray (2 * (nClauses + learnedCap)) L.invalidLiteral

  -- We only need the decision stack to be able to hold all of the literals
  decisionStack <- V.new nLits L.invalidLiteral
  decisionBounds <- V.new nLits (-1)
  varLevels <- GA.newArray nVars (-1)
  seen <- GA.newArray nVars 0
  qref <- P.newRef 0
  highVarRef <- P.newRef highVar
  reasons <- GA.newArray nVars noClause
  pclauses <- GA.newArray (C.clauseCount cnf) undefined

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
  lclauses <- GA.newArray learnedCap undefined
  clAct <- GA.newArray learnedCap 0
  pool <- H.new learnedCap (\a b -> return (a < b)) 0
  F.forM_ [0.. learnedCap - 1] $ \cref -> do
    H.insert pool cref
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
                , eWatchedLiterals = wl
                , eAssignment = assignment
                , eDecisionStack = decisionStack
                , eDecisionBoundaries = decisionBounds
                , eDecisionReasons = reasons
                , ePropagationQueue = qref
                , eProblemClauses = pclauses
                , eLearnedClauses = lclauses
                , eLearnedClauseCount = lccount
                , eClauseRefPool = pool
                , eVarLevels = varLevels
                , eMaxLearnedClauses = maxRef
                , eFirstVar = lowVar
                , eLastVar = highVarRef
                , eVariableOrder = heap
                , eVariableIncrement = varInc
                , eVariableActivity = varAct
                , eClauseIncrement = clauseInc
                , eClauseActivity = clAct
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
initializeWatches :: C.CNF a -> Solver Bool
initializeWatches cnf = do
  e <- ask
  let clauses = eProblemClauses e
      cwl = eClausesWatchingLiteral e
      wl = eWatchedLiterals e
  AT.foldArrayM (watchFirst cwl wl clauses) False (C.clauseArray cnf)
  where
    watchFirst cwl wl clauses hasContradiction ix clause = do
      case C.clauseLiterals clause of
        l1 : l2 : _ -> do
          GA.unsafeWriteArray clauses ix clause
          GA.unsafeWriteArray wl (2 * ix) l1
          GA.unsafeWriteArray wl (2 * ix + 1) l2
          l1w <- GA.readArray cwl l1
          V.push l1w ix
          l2w <- GA.readArray cwl l2
          V.push l2w ix
          return hasContradiction
        l : [] -> do
          validAssertion <- tryAssertLiteral l noClause
          return (not validAssertion || hasContradiction)
        [] -> return hasContradiction

-- | An invalid clause ref, used to denote that a variable was either
-- assigned by a decision or as an asserting literal (or has not been
-- assigned a value yet).
noClause :: ClauseRef
noClause = (-1)

{- Note [Learned Clause Watches]

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
