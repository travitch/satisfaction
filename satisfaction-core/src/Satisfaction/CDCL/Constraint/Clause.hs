-- | The implementation of the 'Constraint' interface for 'CL.Clause's
module Satisfaction.CDCL.Constraint.Clause (
  mkClauseConstraint,
  mkLearnedClauseConstraint
  ) where

import Control.Monad ( when )

import qualified Data.Array.Vector as V
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Ref.Prim as P

import qualified Satisfaction.Formula.Literal as L
import Satisfaction.CDCL.Monad
import qualified Satisfaction.CDCL.Clause as CL
import qualified Satisfaction.CDCL.Core as C
import qualified Satisfaction.Internal.Debug as D

-- | Create a new clausal constraint.
--
-- The signature enforces that clauses must have at least two
-- literals.
mkClauseConstraint :: L.Literal -> L.Literal -> [L.Literal] -> Solver Constraint
mkClauseConstraint l1 l2 rest = do
  cl <- CL.new 0 (l1:l2:rest)
  let con = Constraint clauseInterface cl
  cwl <- asks eClausesWatchingLiteral
  l1w <- GA.readArray cwl l1
  l2w <- GA.readArray cwl l2
  V.push l1w con
  V.push l2w con
  return con

-- | Create a new clausal constraint with the learned flag set
--
-- Note that this also sets up the second watch (on the non-asserted
-- literal) to the first literal that was set at the given decision
-- level (the 'Int').  This is required for correctness.
mkLearnedClauseConstraint :: Int -> L.Literal -> L.Literal -> [L.Literal] -> Solver Constraint
mkLearnedClauseConstraint btLevel l1 l2 rest = do
  -- TODO give an initial activity
  cl <- CL.new 0 (l1:l2:rest)
  CL.setLearnedFlag cl
  let con = Constraint clauseInterface cl
  e <- ask
  lw1 <- GA.unsafeReadArray (eClausesWatchingLiteral e) l1
  V.push lw1 con
  -- Set the second watched literal to the first one that was set
  -- at @btLevel@.
  watchFirstAtLevel btLevel con cl
  return con

watchFirstAtLevel :: Int -> Constraint -> CL.Clause Solver -> Solver ()
watchFirstAtLevel btLevel con cl = do
  nLits <- CL.literalCount cl
  go 1 nLits cl
  where
    go ix nLits c
      | ix >= nLits = error ("impossible: No matching literal/level for watchFirstAtLevel: " ++ show btLevel)
      | otherwise = do
          e <- ask
          lit <- CL.unsafeReadLiteral cl ix
          lvl <- GA.unsafeReadArray (eVarLevels e) (L.var lit)
          case lvl == btLevel of
            False -> go (ix + 1) nLits cl
            True -> do
              lw <- GA.unsafeReadArray (eClausesWatchingLiteral e) lit
              V.push lw con
              CL.unsafeSwapLiterals c 1 ix

clauseInterface :: ConstraintInterface (CL.Clause Solver)
clauseInterface = CI { conRemove = clauseRemove
                     , conPropagate = clausePropagate
                     , conSimplify = clauseSimplify
                     , conReason = clauseReason
                     , conLocked = clauseIsLocked
                     , conReadActivity = \_ -> CL.readActivity
                     , conWriteActivity = \_ -> CL.writeActivity
                     , conAlwaysKeep = clauseAlwaysKeep
                     }

-- | Remove literals that are False.  If the clause is satisfied,
-- return True (which will cause it to be removed).
--
-- We can't fully remove it here because we don't know where it is
-- living (learned vs problem), though we could potentially figure it
-- out.  That might not be true for other constraint types.
clauseSimplify :: Constraint -> CL.Clause Solver -> Solver Bool
clauseSimplify con cl = do
  nLits <- CL.literalCount cl
  go 0 nLits
  where
    go ix nLits
      | nLits == 0 = error "Simplify produced an empty clause"
      | ix >= nLits && ix == 0 = do
          -- We are done and there is only a single literal left -
          -- assert it to be True (and then have it be removed)
          l <- CL.unsafeReadLiteral cl ix
          C.assertLiteral l Nothing
          return True
      | ix >= nLits = return False
      | otherwise = do
          l <- CL.unsafeReadLiteral cl ix
          v <- C.literalValue l
          case v of
            _ | v == L.liftedFalse -> do
                  mNewLit <- CL.removeLiteral cl l
                  when (ix < 2) $ do
                    case mNewLit of
                      Just newLit -> C.watchLiteral con newLit
                      Nothing -> return ()
                  go ix (nLits - 1)
              | v == L.liftedTrue -> return True
              | otherwise -> go (ix + 1) nLits


clauseRemove :: Constraint -> CL.Clause Solver -> Solver ()
clauseRemove con cl = do
  -- Normally, clauses cannot be singletons (or empty).  This checks
  -- for the single literal case because we might be removing a clause
  -- after it has been simplified in the simplifier, which could
  -- potentially shrink the clause that much.
  litCount <- CL.literalCount cl
  when (litCount >= 1) $ do
    l0 <- CL.unsafeReadLiteral cl 0
    C.unwatchLiteral con l0
  when (litCount >= 2) $ do
    l1 <- CL.unsafeReadLiteral cl 1
    C.unwatchLiteral con l1

clauseAlwaysKeep :: Constraint -> CL.Clause Solver -> Solver Bool
clauseAlwaysKeep _con cl = do
  nLits <- CL.literalCount cl
  return (nLits == 2)

clauseIsLocked :: Constraint -> CL.Clause Solver -> Solver Bool
clauseIsLocked con cl = do
  e <- ask
  wl1 <- CL.unsafeReadLiteral cl 0
  r1 <- GA.unsafeReadArray (eDecisionReasons e) (L.var wl1)
  case r1 of
    Nothing -> return False
    Just r1' -> return (r1' == con)

clauseReason :: Constraint -> CL.Clause Solver -> Maybe L.Literal -> Solver [L.Literal]
clauseReason _con cl mLit = do
  bumpClauseActivity cl
  let ix0 = maybe 0 (const 1) mLit
  nLits <- CL.literalCount cl
  go ix0 nLits []
  where
    go ix nLits acc
      | ix >= nLits = return acc
      | otherwise = do
          l <- CL.unsafeReadLiteral cl ix
          go (ix + 1) nLits (l : acc)

-- | Bump the activity of a learned clause.
--
-- Calling this function on a problem (i.e., non-learned) clause is
-- safe and is a no-op
bumpClauseActivity :: CL.Clause Solver -> Solver ()
bumpClauseActivity cl = do
  e <- ask
  isLearned <- CL.readIsLearned cl
  case isLearned of
    False -> return ()
    True -> do
      amount <- P.readRef (eClauseIncrement e)
      act0 <- CL.readActivity cl
      let act1 = act0 + amount
      CL.writeActivity cl act1
      case act1 > C.activityCap of
        False -> return ()
        True -> C.rescaleActivity

-- Propagate

-- | Re-arrange the watched literals in the clause such that the False
-- literal (i.e., the one that needs to be changed) is first.  Return
-- the other literal.
normalizeWatchedLiterals :: CL.Clause Solver -> L.Literal -> Solver L.Literal
normalizeWatchedLiterals cl falseLit = do
  l0 <- CL.unsafeReadLiteral cl 0
  l1 <- CL.unsafeReadLiteral cl 1
  case l1 == falseLit of
    True -> return l0
    False -> do
      CL.unsafeSwapLiterals cl 0 1
      return l1

clausePropagate :: Constraint -> CL.Clause Solver -> L.Literal -> Solver PropagationResult
clausePropagate con cl falseLit = do
  otherLit <- normalizeWatchedLiterals cl falseLit
  otherVal <- C.literalValue otherLit
  case otherVal == L.liftedTrue of
    True -> do
      liftIO $ D.traceIO "      [uw] Satisfied clause"
      return PropagationKeepWatch
    False -> do
      sz <- CL.literalCount cl
      go otherLit (sz - 1)
  where
    go otherLit ix
      | ix < 2 = do
        -- Could not find a new literal to watch, so we have a unit
        -- clause.  We can try to assert the resulting literal, which
        -- could fail if it introduces a contradiction.
        res <- C.tryAssertLiteral otherLit (Just con)
        case res of
          True -> return PropagationKeepWatch
          False -> return PropagationConflict
      | otherwise = do
          lit <- CL.unsafeReadLiteral cl ix
          lv <- C.literalValue lit
          case lv == L.liftedFalse of
            True -> go otherLit (ix - 1)
            False -> do
              e <- ask
              liftIO $ D.traceIO ("    [uw] Now watching " ++ show lit)
              CL.unsafeSwapLiterals cl 1 ix
              newWl <- GA.unsafeReadArray (eClausesWatchingLiteral e) lit
              V.push newWl con
              return PropagationNewWatch
