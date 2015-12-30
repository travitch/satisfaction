{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Main ( main ) where

import Control.Monad.IO.Class ( liftIO )
import qualified Data.Array.IArray as IA
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Mutable as PMA
import qualified Data.Array.Prim.Unboxed.Mutable as PUMA
import qualified Data.Array.Vector as V
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Language.CNF.Parse.ParseDIMACS as P
import qualified System.FilePath.Find as FP
import qualified Test.Tasty as T
import qualified Test.Tasty.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as MQC
import qualified Test.Tasty.HUnit as T

import qualified Data.Array.Heap as H

import qualified Satisfaction.CDCL as S
import qualified Satisfaction.CDCL.Monad as S
import qualified Satisfaction.CDCL.Clause as C
import qualified Satisfaction.CDCL.Constraint as CO
import qualified Satisfaction.Formula as CNF
import qualified Satisfaction.Formula.Literal as L

main :: IO ()
main = do
  satTests <- FP.find FP.always (FP.extension FP.==? ".cnf") "tests/cnf/sat"
  unsatTests <- FP.find FP.always (FP.extension FP.==? ".cnf") "tests/cnf/unsat"
  T.defaultMain $ T.testGroup "Satisfaction Tests" [
    heapTests1 "UnboxedHeapTests1" allocateUnboxedHeap,
    heapTests1 "BoxedHeapTests1" allocateBoxedHeap,
    heapTests2 "UnboxedHeapTests2" allocateUnboxedHeap,
    heapTests2 "BoxedHeapTests2" allocateBoxedHeap,
    clauseTests,
    dimacsTests "SatTests" satTests noExtraAssertion expectSatisfiable,
    dimacsTests "UnsatTests" unsatTests noExtraAssertion expectUnsatisfiable,
    dimacsTests "ConstrainedSatTests" satTests assertFirstTwoEqual constrainedExpectSatisfiable
    ]

-- The dimacs tests

dimacsTests :: String
            -> [FilePath]
            -> (S.CNF Int -> IO (S.Solver ()))
            -> (P.CNF -> S.Solution Int -> T.Assertion)
            -> T.TestTree
dimacsTests name inputs extraAssertion checkTest = T.testGroup name $ map mkTest inputs
  where
    mkTest input = T.testCase input $ do
      ecnf <- P.parseFile input
      case ecnf of
        Left err -> T.assertString (show err)
        Right cnf ->
          case convertCNF cnf of
            Nothing -> T.assertString "No clauses"
            Just cnf' -> do
              extraA <- extraAssertion cnf'
              sol <- S.solve extraA cnf'
              checkTest cnf sol

noExtraAssertion :: a -> IO (S.Solver ())
noExtraAssertion _ = return (return ())

assertFirstTwoEqual :: S.CNF Int -> IO (S.Solver ())
assertFirstTwoEqual cnf = do
  let mv1 = CNF.cnfMapVariable cnf 1
      mv2 = CNF.cnfMapVariable cnf 2
  case (mv1, mv2) of
    (Just v1, Just v2) -> return $ do
      con <- CO.mkEqualityConstraint v1 v2
      e <- S.ask
      V.push (S.eProblemClauses e) con
    _ -> return (return ())

convertCNF :: P.CNF -> Maybe (S.CNF Int)
convertCNF cnf0 =
  S.fromSimpleList $ map fromClause (P.clauses cnf0)
  where
    fromClause c = [ fromDIMACS e
                   | e <- IA.elems c
                   ]
    fromDIMACS e | e < 0 = S.N (abs e)
                 | otherwise = S.L e


expectSatisfiable :: P.CNF -> S.Solution Int -> T.Assertion
expectSatisfiable _  S.Unsatisfiable {} = T.assertFailure "Expected satisfying assignment"
expectSatisfiable cnf S.Satisfiable { S.solutionModel = sol } = mapM_ assertAtLeastOneTrue (P.clauses cnf)
  where
    assignment = S.satisfyingAssignment sol
    assertAtLeastOneTrue clause = do
      let litVal :: Int -> IO Bool
          litVal l | l < 0 = maybe msg (return . not) (lookup (abs l) assignment)
                   | otherwise = maybe msg return (lookup l assignment)
            where
              msg = error ("Expected assignment for lit " ++ show l)
      clauseValue <- mapM litVal (IA.elems clause)
      T.assertBool ("Expected clause to be true: " ++ show clause) (or clauseValue)

-- These are satisfiable tests with some extra constraints asserted.
-- The extra constraints might make them unsat, which is fine.
--
-- If they come back satisfiable, check that the extra assertion
-- really holds.
constrainedExpectSatisfiable :: P.CNF -> S.Solution Int -> T.Assertion
constrainedExpectSatisfiable _ S.Unsatisfiable {} = return ()
constrainedExpectSatisfiable cnf S.Satisfiable { S.solutionModel = sol } = do
  -- Make sure that each clause is still satisfied
  mapM_ assertAtLeastOneTrue (P.clauses cnf)
  -- Now make sure that v0 == v1
  T.assertBool "First two variables equal" (lookup 1 assignment == lookup 2 assignment)
  where
    assignment = S.satisfyingAssignment sol
    assertAtLeastOneTrue clause = do
      let litVal :: Int -> IO Bool
          litVal l | l < 0 = maybe msg (return . not) (lookup (abs l) assignment)
                   | otherwise = maybe msg return (lookup l assignment)
            where
              msg = error ("Expected assignment for lit " ++ show l)
      clauseValue <- mapM litVal (IA.elems clause)
      T.assertBool ("Expected clause to be true: " ++ show clause) (or clauseValue)

expectUnsatisfiable :: P.CNF -> S.Solution Int -> T.Assertion
expectUnsatisfiable _ sol =
  case sol of
    S.Unsatisfiable {} -> return ()
    _ -> T.assertFailure "Unexpected solution"

-- Setup for the binary heap tests

intComparator :: Int -> Int -> IO Bool
intComparator a b = return (a < b)

allocateUnboxedHeap :: Int -> IO (H.Heap PUMA.MArray IO Int)
allocateUnboxedHeap range = H.new range intComparator (-1)

allocateBoxedHeap :: Int -> IO (H.Heap PMA.MArray IO Int)
allocateBoxedHeap range = H.new range intComparator (-1)

-- Tests that adding a bunch of elements to the heap and removing the
-- minimum actually returns the true minimum element.
heapTests1 :: (GA.PrimMArray a Int) => String -> (Int -> IO (H.Heap a IO Int)) -> T.TestTree
heapTests1 name allocator = QC.testProperty name $ MQC.monadicIO $ do
  let testRange = (0, 10000)
  nElts <- MQC.pick (QC.choose (0, 20))
  lst <- MQC.pick (QC.vectorOf nElts (QC.choose testRange))
  -- arbitrary can generate a negative number - we only want positive
  -- numbers here (including not zero, so always add at least one)
  h <- liftIO $ allocator (snd testRange + 1)
  let minElt = minimum lst
  F.forM_ lst $ \i -> liftIO $ H.unsafeInsert h i
  mfromHeap <- liftIO $ H.takeMin h
  -- We are allowed to get Nothing (and should) if there were no
  -- elements in the heap
  case mfromHeap of
    Nothing -> MQC.assert (null lst)
    Just elt -> MQC.assert (elt == minElt)

heapTests2 :: (GA.PrimMArray a Int) => String -> (Int -> IO (H.Heap a IO Int)) -> T.TestTree
heapTests2 name allocator = QC.testProperty name $ MQC.monadicIO $ do
  let testRange = (0, 10000)
  nElts <- MQC.pick (QC.choose (0, 20))
  lst <- MQC.pick (QC.vectorOf nElts (QC.choose testRange))
  -- arbitrary can generate a negative number - we only want positive
  -- numbers here (including not zero, so always add at least one)
  h <- liftIO $ allocator (snd testRange + 1)
  F.forM_ lst $ \i -> liftIO $ H.unsafeInsert h i
  F.forM_ (L.nub (L.sort lst)) $ \expectedElt -> do
    mfromHeap <- liftIO $ H.takeMin h
    case mfromHeap of
      Nothing -> MQC.assert False
      Just elt -> MQC.assert (elt == expectedElt)
  mfromHeap <- liftIO $ H.takeMin h
  MQC.assert (mfromHeap == Nothing)

-- Test the implementation of Clauses to ensure that all of the
-- manually-specified offsets are correct.
clauseTests :: T.TestTree
clauseTests = T.testGroup "clauseTests" [
  testClauseMetadata
  ]

testClauseMetadata :: T.TestTree
testClauseMetadata = T.testCase "clauseMetadata" $ do
  let activity = 3.4
      lits0 = [ L.MkLiteral 5, L.MkLiteral 10, L.MkLiteral 0 ]
  c <- C.new activity lits0
  act0 <- C.readActivity c
  nLits0 <- C.literalCount c
  isLearned0 <- C.readIsLearned c
  T.assertEqual "Expected activity" activity act0
  T.assertEqual "Expected literal count" (length lits0) nLits0
  T.assertEqual "Expected initial flags" False isLearned0

  F.forM_ [0..length lits0 - 1] $ \ix -> do
    lit <- C.readLiteral c ix
    T.assertEqual "Expected literal" (lits0 !! ix) lit

  -- Now perform some updates to ensure we aren't clobbering expected values
  let activity1 = 11.4
  C.writeActivity c activity1
  act1 <- C.readActivity c
  nLits1 <- C.literalCount c
  isLearned1 <- C.readIsLearned c
  T.assertEqual "Expected activity" activity1 act1
  T.assertEqual "Expected literal count" (length lits0) nLits1
  T.assertEqual "Expected initial flags" False isLearned1

  F.forM_ [0..length lits0 - 1] $ \ix -> do
    lit <- C.readLiteral c ix
    T.assertEqual "Expected literal" (lits0 !! ix) lit

  -- Set learned
  C.setLearnedFlag c
  act2 <- C.readActivity c
  nLits2 <- C.literalCount c
  isLearned2 <- C.readIsLearned c
  T.assertEqual "Expected activity" activity1 act2
  T.assertEqual "Expected literal count" (length lits0) nLits2
  T.assertEqual "Expected initial flags" True isLearned2

  F.forM_ [0..length lits0 - 1] $ \ix -> do
    lit <- C.readLiteral c ix
    T.assertEqual "Expected literal" (lits0 !! ix) lit

  -- Swap two variables to make sure it doesn't clobber metadata
  l0 <- C.readLiteral c 0
  l2 <- C.readLiteral c 2
  C.writeLiteral c 0 l2
  C.writeLiteral c 2 l0
  act3 <- C.readActivity c
  nLits3 <- C.literalCount c
  isLearned3 <- C.readIsLearned c
  T.assertEqual "Expected activity" activity1 act3
  T.assertEqual "Expected literal count" (length lits0) nLits3
  T.assertEqual "Expected initial flags" True isLearned3

  let exLits2 = [lits0 !! 2, lits0 !! 1, lits0 !! 0]
  F.forM_ [0..length lits0 - 1] $ \ix -> do
    lit <- C.readLiteral c ix
    T.assertEqual "Expected literal" (exLits2 !! ix) lit

