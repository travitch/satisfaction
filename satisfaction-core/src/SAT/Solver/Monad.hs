{-# LANGUAGE ExistentialQuantification #-}
-- | These are internal types for the solver
--
-- These types are internal and specific to the CDCL solver.  More
-- reusable types are in the SAT.* namespace.
module SAT.Solver.Monad (
  Conflict(..),
  Solver,
  runSolver,
  ask,
  asks,
  liftIO,
  assertLiteral,
  withNextDecidedLiteral,
  withQueuedDecision,
  assignVariableValue,
  resetVariable,
  getDecisionLevel,
  incrementDecisionLevel,
  getFirstVariable,
  getLastVariable,
  lookupVariableAssignment,
  lookupVariableState,
  updateWatchlists,
  undoDecisionLevel,
  extractAssignment
  ) where

import Control.Applicative
import Control.Monad ( ap )
import qualified Data.Array.Prim as PA
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Prim.Unboxed as PUA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import Data.Bits ( shiftL )
import qualified Data.Foldable as F
import Data.IORef
import Data.Ix ( range, rangeSize )
import qualified Data.Set as S

import qualified Data.Array.Traverse as AT
import qualified Data.Array.Vector as V
import qualified SAT.CNF as C
import qualified SAT.Literal as L
import qualified SAT.Solver.Debug as D

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
  Watchlist { wlLitWatches :: PMA.MArray IO L.Literal (V.Vector PUMA.MArray IO ClauseNumber)
              -- ^ This array is of length @2n@.  Index @i@ is the
              -- list of clauses (by index) watching literal @i@.
              -- Index @2i+1@ is the list of clauses watching @~i@.
            , wlClauseWatches :: PUMA.MArray IO ClauseNumber L.Literal
              -- ^ The array is of length @2c@ where @c@ is the number
              -- of clauses.  Index @2i@ is the first literal being
              -- watched for clause @i@.  Index @2i+1@ is the second
              -- literal being watched for clause @i@.
            }

-- | The Reader environment.  We quantify away the type parameter to
-- the formula because we never need to look at its reverse mapping
-- back to user-provided variables.
--
-- The last variable is an IORef because we may want to add new variables
-- internally later (e.g., for SMT solving).
data Env = forall a . Env { eWatchlist :: Watchlist
                          , eAssignment :: PUMA.MArray IO L.Variable L.Value
                          , eVarStates :: PUMA.MArray IO L.Variable L.State
                          , eDecisionStack :: V.Vector PUMA.MArray IO L.Literal
                            -- ^ A record of the decisions made
                          , eDecisionBoundaries :: V.Vector PUMA.MArray IO Int
                            -- ^ Boundary markers between decision
                            -- levels in the decision stack.
                          , eVarLevels :: PUMA.MArray IO L.Variable Int
                            -- ^ The decision level for each variable.
                          , ePropagationQueue :: {-# UNPACK #-} !(IORef Int)
                            -- ^ Literals that have been assigned
                            -- False that we need to propagate units
                            -- for.  This is an index into the
                            -- decision stack.
                          , eFirstVar :: L.Variable
                          , eLastVar :: IORef L.Variable
                          , eNextVar :: IORef L.Variable
                            -- ^ The next variable to assign when we have to make a decision
                          , eCNF :: C.CNF a
                          }



-- | A description of a conflict that tells us what conflict clause we
-- should learn.
data Conflict = Conflict

-- | This function is called on a 'Literal' whose value has been decided.
--
-- The task here is to look up all of the clauses that were watching
-- @¬lit@ and update their watchlists.
--
-- If a clause becomes unit, we have two options:
--
-- * Either we can make an assignment to make it True, or
--
-- * We cannot (due to a conflict)
--
-- In the first case, we make the assignment (which implicitly adds
-- that newly decided literal to the queue).  Otherwise, we invoke the
-- conflict continuation, which will backtrack and drain the queue
-- (since those assignments are being undone, we do not need to
-- propagate their units).
--
-- During this process, we remove elements from the inverse watchlist
-- (the list of clauses watching each literal) as we find new watched
-- variables.  In the case we cannot find a new watch (because the
-- clause is unit), we leave the entry in the inverse watchlist.  This
-- way, the watchlist is consistent after we backtrack.  In the case
-- we don't backtrack the decision, it doesn't matter because the
-- clause is satisfied.
updateWatchlists :: L.Literal -- ^ Literal causing the update
                 -> (Conflict -> Solver a) -- ^ Continuation on a conflicting assignment
                 -> Solver a -- ^ Continuation on successful watchlist update
                 -> Solver a
updateWatchlists l kConflict kNext = do
  e <- ask
  let clauses = case e of
                   Env { eCNF = cnf } -> C.clauseArray cnf
      wl = eWatchlist e
  clausesWatching <- liftIO $ GA.unsafeReadArray (wlLitWatches wl) falseLit
  go clauses clausesWatching 0
  where
    falseLit = L.neg l
    -- This is invoked if we can't find another literal to watch.
    -- This means that the clause is unit and we can try to satisfy it
    -- by satisfying the remaining variable.
    kUnit clauseNum otherLit watchers clauses ix = do
      liftIO $ D.traceIO ("      [uw] Clause is unit: " ++ show clauseNum)
      val <- literalValue otherLit
      -- If the other literal is unassigned, we can assign it (and
      -- implicitly enqueue it to propagate units).  It cannot be
      -- True, because we handle that in a case of 'go' (see the
      -- otherVal == liftedTrue check)
      --
      -- Otherwise, we have a conflict.  Clean up and then backtrack.
      -- We can get a conflict (despite watchlist tracking) if we made
      -- an assignment that cause a conflict, but the conflicting
      -- update is in the queue and not processed yet.
      case () of
        _ | L.isUnassigned val -> do
              liftIO $ D.traceIO ("    [uw] Asserting a literal during watchlist update: " ++ show otherLit)
              assertLiteral otherLit
              go clauses watchers (ix + 1)
          | otherwise -> do
              liftIO $ D.traceIO ("    [uw] Encountered a unit conflict due to " ++ show otherLit ++ ", which is assigned " ++ show val)
              kConflict Conflict
    go clauses watchers ix = do
      sz <- liftIO $ V.size watchers
      case ix < sz of
        False -> do
          liftIO $ D.traceIO ("      [uw] Successfully updated all watches")
          -- We have successfully found a new set of consistent
          -- watches
          kNext
        True -> do
          clauseNum <- liftIO $ V.unsafeReadVector watchers ix
          let cl = clauses PA.! clauseNum
          liftIO $ D.traceIO ("      [uw] Updating watches for clause " ++ show cl)
          normalizeWatchedLiterals clauseNum falseLit $ \otherLit falseLitIndex -> do
            wl <- asks eWatchlist
            -- falseLit is @¬l@ and known to be false.  It is at the
            -- given index.  We have to check to see if the other lit
            -- is true; if so, this clause is satisfied and we don't
            -- need to update anything.
            otherVal <- literalValue otherLit
            case otherVal == L.liftedTrue of
              True -> do
                -- The clause is satisfied, so we don't need to change our watches at all.
                liftIO $ D.traceIO "      [uw] Satisfied clause"
                go clauses watchers (ix + 1)
              False -> do
                -- Find a new lit to watch instead of falseLit.  If
                -- this succeeds, we need to remove the clause at @ix@
                -- (which is @clauseNum@) and add @clauseNum@ to the appropriate list
                let whenUnit = kUnit clauseNum otherLit watchers clauses ix
                withTrueOrUnassignedLiteral whenUnit cl otherLit $ \newWatchedLit -> do
                  liftIO $ GA.unsafeWriteArray (wlClauseWatches wl) falseLitIndex newWatchedLit
                  liftIO $ V.removeElement watchers ix
                  watchingLit <- liftIO $ GA.unsafeReadArray (wlLitWatches wl) newWatchedLit
                  liftIO $ V.unsafePush watchingLit clauseNum
                  -- We don't increment @ix@ because we removed the
                  -- element that was at @ix@ and replaced it with a
                  -- new one, so we need to check ix again.
                  go clauses watchers ix
{-# INLINE updateWatchlists #-}

-- | Determine the value of the given 'L.Literal
literalValue :: L.Literal -> Solver L.Value
literalValue l = do
  assignments <- asks eAssignment
  val <- liftIO $ GA.unsafeReadArray assignments (L.var l)
  return $! L.litValue l val
{-# INLINE literalValue #-}

-- | Analyze the currently watched literals for a clause and figure
-- out which index holds the one we know to be false and which holds
-- the other.
--
-- Calls the continuation with the other literal and the index in the
-- watchlist of the false literal.  The position will be overwritten
-- with a new watched literal by the continuation, if possible.
normalizeWatchedLiterals :: Int -> L.Literal -> (L.Literal -> Int -> Solver a) -> Solver a
normalizeWatchedLiterals clauseNum falseLit k = do
  wl <- asks eWatchlist
  let watchArray = wlClauseWatches wl
  watch1 <- liftIO $ GA.unsafeReadArray watchArray watch1Ix
  watch2 <- liftIO $ GA.unsafeReadArray watchArray watch2Ix
  case watch1 == falseLit of
    True -> k watch2 watch1Ix
    False -> k watch1 watch2Ix
  where
    watch1Ix = clauseNum `shiftL` 1
    watch2Ix = watch1Ix + 1
{-# INLINE normalizeWatchedLiterals #-}

withTrueOrUnassignedLiteral :: Solver a -- ^ Continuation for the case we can't find a new literal to watch
                            -> C.Clause -- ^ The clause to search
                            -> L.Literal -- ^ The literal we don't want to choose (because we are already watching it)
                            -> (L.Literal -> Solver a) -- ^ The continuation to call with the new literal
                            -> Solver a
withTrueOrUnassignedLiteral kConflict clause ignoreLit withLit = go 0
  where
    sz = C.clauseSize clause
    go ix | ix >= sz = kConflict
          | otherwise = do
              let l = clause `C.clauseLiteral` ix
              case l == ignoreLit of
                True -> go (ix + 1)
                False -> do
                  lv <- literalValue l
                  case lv == L.liftedFalse of
                    False -> withLit l
                    True -> go (ix + 1)
{-# INLINE withTrueOrUnassignedLiteral #-}


-- | For the next 'Literal' that has been decided in the queue, call
-- the given continuation.  If there are no more literals in the
-- queue, call the empty queue continuation.
--
-- The queue is embedded in the decision stack.  'ePropagationQueue'
-- points to the next literal in the queue.  Before we pass a literal
-- to the continuation, we have to advance the queue pointer.
withQueuedDecision :: Solver a -- ^ Called when the queue is empty
                   -> (L.Literal -> Solver a) -- ^ Called on each 'Literal' in the queue
                   -> Solver a
withQueuedDecision kEmpty kProp = do
  e <- ask
  let dvec = eDecisionStack e
      qref = ePropagationQueue e
  decisionIndex <- liftIO $ readIORef qref
  sz <- liftIO $ V.size dvec
  case decisionIndex >= sz of
    True -> kEmpty
    False -> do
      lit <- liftIO $ V.unsafeReadVector dvec decisionIndex
      liftIO $ modifyIORef' qref (+1)
      kProp lit
{-# INLINE withQueuedDecision #-}

-- | Undo all of the assignments until we reach a decision level for which
-- we can flip the assignment of the decided variable (from true to
-- false or false to true).
--
-- This can undo more than one decision level.
--
-- If we undo the lowest decision level, we have found a contradiction
-- and call @kUnsat@.
undoDecisionLevel :: Solver a -- ^ Unsatisfiable continuation
                  -> Solver a -- ^ Normal continuation
                  -> (L.Literal -> Solver ()) -- ^ Callback for each literal
                  -> Solver a
undoDecisionLevel kUnsat kDone k = go
  where
    go = do
      e <- ask
      dl <- getDecisionLevel
      let vec = eDecisionStack e
          boundaries = eDecisionBoundaries e
      nDecisions <- liftIO $ V.size vec
      nBounds <- liftIO $ V.size boundaries
      lastBound <- liftIO $ V.unsafeReadVector boundaries (nBounds - 1)
      let nLits = nDecisions - lastBound
      levelBaseLit <- liftIO $ V.unsafeReadVector vec lastBound
      let levelBaseVar = L.var levelBaseLit
      levelBaseState <- liftIO $ GA.unsafeReadArray (eVarStates e) levelBaseVar
      liftIO $ D.traceIO ("  [bt] Current decision level is " ++ show dl ++ ", which begins at stack index " ++ show lastBound ++ ", encompassing " ++ show nLits ++ " literals")
      -- If we tried both, backtrack again.  If we can't backtrack
      -- anymore, call the unsat continuation
      let canAssignBTVar = levelBaseState /= L.triedBoth
      case not canAssignBTVar && dl == 1 of
        True -> kUnsat
        False -> do
          undo vec lastBound nDecisions
          liftIO $ D.traceIO ("  [bt] Done undoing decisions, fixing metadata.  Popping " ++ show nLits
                              ++ " literals.  Last boundary is now: " ++ show lastBound)
          liftIO $ D.traceIO ("    [bt] State of " ++ show levelBaseVar ++ " is " ++ show levelBaseState)
          liftIO $ V.pop vec nLits
          liftIO $ V.pop boundaries 1
          liftIO $ writeIORef (ePropagationQueue e) lastBound
          case canAssignBTVar of
            False -> go
            True -> do
              -- Restore the state of the next variable we will try to assign
              liftIO $ GA.unsafeWriteArray (eVarStates e) levelBaseVar levelBaseState
              liftIO $ writeIORef (eNextVar e) levelBaseVar
              kDone
    undo s ix nDecisions
      | ix >= nDecisions = return ()
      | otherwise = do
          lit <- liftIO $ V.unsafeReadVector s ix
          k lit
          undo s (ix + 1) nDecisions
{-# INLINE undoDecisionLevel #-}

getLastVariable :: Solver L.Variable
getLastVariable = do
  ref <- asks eLastVar
  liftIO $ readIORef ref
{-# INLINE getLastVariable #-}

getFirstVariable :: Solver L.Variable
getFirstVariable = asks eFirstVar
{-# INLINE getFirstVariable #-}

-- | Find the next 'Variable' to assign a value to, implicitly
-- encoding that as a 'Literal'.
--
-- If there are no more variables to assign, extract a solution with
-- the given continuation.
withNextDecidedLiteral :: Solver a -- ^ Continue into the done state (i.e., extract a solution)
                       -> (L.Literal -> Solver a) -- ^ Continue with selected 'Literal'
                       -> Solver a
withNextDecidedLiteral kDone kLit = do
  e <- ask
  nv <- liftIO $ readIORef (eNextVar e)
  lv <- liftIO $ readIORef (eLastVar e)
  go e lv nv
  where
    go e lv nv
      | nv > lv = kDone
      | otherwise = do
          state <- liftIO $ GA.unsafeReadArray (eVarStates e) nv
          dl <- liftIO $ GA.unsafeReadArray (eVarLevels e) nv
          case () of
            _ | dl >= 0 || state == L.triedBoth -> do
                  liftIO $ D.traceIO ("[WNDL] Skipping already assigned var " ++ show nv ++ " because " ++ show (dl, state))
                  go e lv (L.nextVariable nv)
              | otherwise -> do
                  liftIO $ writeIORef (eNextVar e) (L.nextVariable nv)
                  kLit (L.nextLiteral nv state)
{-# INLINE withNextDecidedLiteral #-}

assertLiteral :: L.Literal -> Solver ()
assertLiteral lit = do
  e <- ask
  let var = L.var lit
      val = L.satisfyLiteral lit
  curState <- liftIO $ GA.unsafeReadArray (eVarStates e) var
  assignVariableValue var val (L.nextValueState val curState)
  liftIO $ V.unsafePush (eDecisionStack e) lit
{-# INLINE assertLiteral #-}

getDecisionLevel :: Solver Int
getDecisionLevel = do
  bv <- asks eDecisionBoundaries
  liftIO (V.size bv)
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
  dl <- liftIO $ V.size (eDecisionStack e)
  liftIO $ V.unsafePush (eDecisionBoundaries e) dl
  level <- getDecisionLevel
  liftIO $ D.traceIO ("[idl] At decision level " ++ show level ++ ", which starts at index " ++ show dl)
{-# INLINE incrementDecisionLevel #-}

-- | Assign a 'L.Value' to a 'L.Variable'.
--
-- Note that the 'State' is always required to be updated at the same
-- time.
assignVariableValue :: L.Variable -> L.Value -> L.State -> Solver ()
assignVariableValue var val st = do
  e <- ask
  dl <- getDecisionLevel
  liftIO $ do
    D.traceIO ("  [assign] Assigning " ++ show val ++ " to " ++ show var)
    GA.unsafeWriteArray (eAssignment e) var val
    GA.unsafeWriteArray (eVarStates e) var st
    GA.unsafeWriteArray (eVarLevels e) var dl
{-# INLINE assignVariableValue #-}

resetVariable :: L.Variable -> Solver ()
resetVariable var = do
  e <- ask
  liftIO $ do
    D.traceIO ("[reset] Setting the state of " ++ show var ++ " to triedNothing")
    GA.unsafeWriteArray (eAssignment e) var L.unassigned
    GA.unsafeWriteArray (eVarStates e) var L.triedNothing
    GA.unsafeWriteArray (eVarLevels e) var (-1)
{-# INLINE resetVariable #-}

lookupVariableAssignment :: L.Variable -> Solver L.Value
lookupVariableAssignment var = do
  vals <- asks eAssignment
  liftIO $ GA.unsafeReadArray vals var
{-# INLINE lookupVariableAssignment #-}

lookupVariableState :: L.Variable -> Solver L.State
lookupVariableState var = do
  states <- asks eVarStates
  liftIO $ GA.unsafeReadArray states var
{-# INLINE lookupVariableState #-}

extractAssignment :: Solver (PUA.Array L.Variable L.Value)
extractAssignment = do
  a <- asks eAssignment
  liftIO $ PUMA.freeze a

-- | A context in which a solver runs.  This is basically a ReaderT IO.
newtype Solver a = S { runS :: Env -> IO a }

-- | Run a solver with an environment set up for a given CNF formula.
runSolver :: C.CNF b -> Solver a -> IO a
runSolver cnf comp = do
  let vrange@(lowVar, highVar) = variableRange cnf
      lrange = (L.toPositiveLiteral lowVar, L.toNegativeLiteral highVar)
      nLits = rangeSize lrange
      nVars = rangeSize vrange
  -- There is an assignment for each variable
  assignment <- GA.newArray nVars L.unassigned
  watchlist <- allocateWatchlist cnf lrange
  -- We only need the decision stack to be able to hold all of the literals
  decisionStack <- V.new nLits L.invalidLiteral
  decisionBounds <- V.new nLits (-1)
  varLevels <- GA.newArray nVars (-1)
  qref <- newIORef 0
  -- We get an initial worklist composed of all of the unit clauses
  states <- GA.newArray nVars L.triedNothing
  highVarRef <- newIORef highVar
  nextVarRef <- newIORef lowVar
  let env = Env { eCNF = cnf
                , eAssignment = assignment
                , eVarStates = states
                , eDecisionStack = decisionStack
                , eDecisionBoundaries = decisionBounds
                , ePropagationQueue = qref
                , eWatchlist = watchlist
                , eVarLevels = varLevels
                , eFirstVar = lowVar
                , eLastVar = highVarRef
                , eNextVar = nextVarRef
                }

  runS (initializeWatches cnf >> comp) env

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

allocateWatchlist :: C.CNF a -> (L.Literal, L.Literal) -> IO Watchlist
allocateWatchlist cnf lrange = do
  litWatches <- GA.newArray_ nLits
  F.forM_ lits $ \l -> do
    v <- V.new nClauses (-1)
    GA.unsafeWriteArray litWatches l v
  clauseWatches <- GA.newArray (2 * nClauses) L.invalidLiteral
  return $ Watchlist { wlLitWatches = litWatches
                     , wlClauseWatches = clauseWatches
                     }
  where
    nClauses = C.clauseCount cnf
    lits = range lrange
    nLits = rangeSize lrange

-- | Initialize the watches.  Each clause starts by watching its first
-- two literals.  Clauses with only one literal are unit clauses,
-- whose literals are automatically inserted into the worklist
--
-- Returns the list of literals comprising unit clauses.  These can be
-- assigned up front.
initializeWatches :: C.CNF a -> Solver ()
initializeWatches cnf = do
  wl <- asks eWatchlist
  AT.mapArrayM_ (watchFirst wl) (C.clauseArray cnf)
  where
    watchFirst wl ix clause = do
      case C.clauseLiterals clause of
        l1 : l2 : _ -> liftIO $ do
          GA.writeArray (wlClauseWatches wl) (2 * ix) l1
          GA.writeArray (wlClauseWatches wl) (2 * ix + 1) l2
          let varWatches = wlLitWatches wl
          l1w <- GA.readArray varWatches l1
          V.push l1w ix
          l2w <- GA.readArray varWatches l2
          V.push l2w ix
        l : [] -> do
          assertLiteral l
          liftIO $ do
            GA.writeArray (wlClauseWatches wl) (2 * ix) l
            GA.writeArray (wlClauseWatches wl) (2 * ix + 1) l
            let varWatches = wlLitWatches wl
            lw <- GA.readArray varWatches l
            V.push lw ix
        [] -> return ()

-- Basic helpers

-- | It is not possible to construct a 'CNF' instance with no clauses
-- (or an empty clause), so there is always at least one literal and
-- this is total.
findRangeWith :: (Ord b) => (L.Literal -> b) -> C.CNF a -> (b, b)
findRangeWith f cnf = (S.findMin s, S.findMax s)
  where
    s = S.fromList [ f l | c <- C.clauseList cnf, l <- C.clauseLiterals c ]

variableRange :: C.CNF a -> (L.Variable, L.Variable)
variableRange = findRangeWith L.var
