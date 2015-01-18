{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
module SAT.Solver (
  solve,
  Solution( Unsat, Solution, satisfyingAssignment ),
  C.CNF,
  C.Lit(..),
  C.fromSimpleList
  ) where

import Control.Applicative
import Control.Monad ( ap )
import qualified Data.Array.IArray as A
import qualified Data.Array.IO as MA
import qualified Data.Array.Unboxed as A
import Data.Int ( Int8 )
import Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import Data.Sequence ( Seq )
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import qualified SAT.CNF as C
import qualified SAT.Literal as L
import SAT.Solver.Types

data Solution a = Unsat
                | Solution { _solutionFormula :: C.CNF a
                           , _rawSolution :: AnAssignment
                           , satisfyingAssignment :: [(a, Bool)]
                           }
                deriving (Eq, Ord, Show)

type AnAssignment = A.UArray Int Value

solve :: C.CNF a -> IO (Solution a)
solve cnf = runSolver cnf go
  where
    go = do
      mconflict <- propagateUnits
      case mconflict of
        Nothing -> do
          allAssigned <- checkAssignment
          case allAssigned of
            True -> return undefined -- satisfiable
            False -> decide >> go
        Just _ -> backtrack >> go -- TODO Analyze conflict

propagateUnits :: Solver (Maybe ())
propagateUnits = do
  mlit <- takeWork
  case mlit of
    Nothing -> return Nothing
    Just _lit -> do
      propagateUnits

checkAssignment :: Solver Bool
checkAssignment = undefined

decide :: Solver ()
decide = undefined

backtrack :: Solver ()
backtrack = undefined

-- solve :: C.CNF a -> IO (Solution a)
-- solve cnf = runSolver cnf $ do
--   -- FIXME: First, assign all of the singleton clauses.  We could find
--   -- a contradiction from them, but more importantly, we didn't set up
--   -- watches for them.
--   sol <- assignVariable 0
--   case sol of
--     Nothing -> return Unsat
--     Just assignment -> do
--       let mapping = [ (C.fromInt cnf A.! ix, b /= 0)
--                     | (ix, b) <- A.assocs assignment
--                     ]
--       return $ Solution cnf assignment mapping

-- assignVariable :: C.Variable -> Solver (Maybe AnAssignment)
-- assignVariable vnum = do
--   Env { eCNF = cnf
--       , eVarStates = states
--       , eAssignment = assignment
--       } <- ask
--   -- Cache this in the env
--   let totalVars = C.variableCount cnf
--   case vnum < totalVars of
--     -- We processed every variable and the current assignment is a solution.
--     False -> do
--       -- FIXME: Need to eventually serialize state here
--       pureArray <- liftIO $ MA.freeze assignment
--       return (Just pureArray)
--     True -> do
--       vstate0 <- liftIO $ MA.readArray (unStates states) vnum
--       case vnum of
--         -- We backtracked all the way to the first variable and have
--         -- already tried all possible assignments to it.  There are no solutions
--         0 | vstate0 == 3 -> return Nothing
--         -- We have tried all possible assignments for the current variable
--         -- (none are valid), so we must backtrack
--         _ | vstate0 == 3 -> backtrack vnum
--         -- Try to assign 0, then 1.  If both fail, backtrack
--         _ -> tryAssignment vnum 0 (tryAssignment vnum 1 (backtrack vnum))

-- -- FIXME: Make vnum a parameter to the continuations her

-- -- | Try to assign the given value to the variable.  If the assignment
-- -- causes a conflict, run the failure continuation.  That will either
-- -- try to assign the opposite value or start backtracking.
-- {-# INLINE tryAssignment #-}
-- tryAssignment :: C.Variable -> Value -> Solver (Maybe AnAssignment) -> Solver (Maybe AnAssignment)
-- tryAssignment vnum value onFailure = do
--   Env { eVarStates = states
--       , eAssignment = assignment
--       } <- ask
--   s <- liftIO $ MA.readArray (unStates states) vnum
--   case (s `shiftR` fromIntegral value) .&. 1 == 0 of
--     False -> onFailure
--     True -> do
--       liftIO $ do
--         MA.writeArray (unStates states) vnum (s .|. (1 `shiftL` fromIntegral value))
--         MA.writeArray assignment vnum value
--       r <- updateWatchlist ((vnum `shiftL` 1) .|. fromIntegral value)
--       case r of
--         CausedConflict -> do
--           liftIO $ MA.writeArray assignment vnum (-1)
--           onFailure
--         NoConflict -> assignVariable (vnum + 1)

-- {-# INLINE backtrack #-}
-- backtrack :: C.Variable -> Solver (Maybe AnAssignment)
-- backtrack vnum
--   | vnum == 0 = return Nothing -- Unsat
--   | otherwise = do
--     Env { eVarStates = states
--         , eAssignment = assignment
--         } <- ask
--     liftIO $ do
--       MA.writeArray (unStates states) vnum 0
--       MA.writeArray assignment vnum (-1)
--     assignVariable (vnum - 1)

-- data Conflict = CausedConflict | NoConflict

-- -- | We just assigned False to the given literal (which is an index
-- -- into the watchlists array).
-- --
-- -- Update each affected clause to watch a new literal.
-- updateWatchlist :: Int -> Solver Conflict
-- updateWatchlist assignedFalseTo = do
--   Env { eWatches = WL watches } <- ask
--   wl <- liftIO $ MA.readArray watches assignedFalseTo
--   -- Assign a different watch
--   watchAlternative watches wl
--   where
--     watchAlternative watches wl =
--       case Seq.viewl wl of
--         Seq.EmptyL -> do
--           -- Everything updated successfully
--           liftIO $ MA.writeArray watches assignedFalseTo Seq.empty
--           return NoConflict
--         clauseNum Seq.:< rest -> do
--           -- Look for the next clause we can watch instead.
--           Env { eCNF = cnf, eAssignment = assignment } <- ask
--           malt <- case C.clause cnf clauseNum of
--             Nothing -> error ("Invalid clause number " ++ show clauseNum)
--             Just c ->
--               let (_, bend) = A.bounds c
--               in takeFirstAlternative assignment c bend
--           case malt of
--             Nothing -> return CausedConflict
--             Just alt -> do
--               wl' <- liftIO $ MA.readArray watches alt
--               liftIO $ MA.writeArray watches alt (wl' Seq.|> clauseNum)
--               liftIO $ MA.writeArray watches assignedFalseTo rest
--               watchAlternative watches rest
--     takeFirstAlternative assignment c ix
--       | ix < 0 = return Nothing
--       | otherwise = do
--         let alt = c A.! ix
--             v = alt `shiftR` 1
--             a = alt .&. 1
--         assigned <- liftIO $ MA.readArray assignment v
--         case assigned < 0 || fromIntegral assigned == a `xor` 1 of
--           True -> return (Just alt)
--           False -> takeFirstAlternative assignment c (ix - 1)




