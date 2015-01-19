{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Main ( main ) where

import Control.Monad.IO.Class ( liftIO )
import qualified Data.Array.IArray as A
import qualified Data.Array.IO as IOA
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Language.CNF.Parse.ParseDIMACS as P
import qualified System.FilePath.Find as FP
import qualified Test.Tasty as T
import qualified Test.Tasty.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as MQC
import qualified Test.Tasty.HUnit as T

import qualified Data.Array.Heap as H
import qualified SAT.Solver as S

main :: IO ()
main = do
  satTests <- FP.find FP.always (FP.extension FP.==? ".cnf") "tests/cnf/sat"
  unsatTests <- FP.find FP.always (FP.extension FP.==? ".cnf") "tests/cnf/unsat"
  T.defaultMain $ T.testGroup "Satisfaction Tests" [
    heapTests1 "UnboxedHeapTests1" allocateUnboxedHeap,
    heapTests1 "BoxedHeapTests1" allocateBoxedHeap,
    heapTests2 "UnboxedHeapTests2" allocateUnboxedHeap,
    heapTests2 "BoxedHeapTests2" allocateBoxedHeap,
    dimacsTests "SatTests" satTests expectSatisfiable,
    dimacsTests "UnsatTests" unsatTests expectUnsatisfiable
    ]

-- The dimacs tests

dimacsTests :: String -> [FilePath] -> (P.CNF -> Maybe (S.Solution Int) -> T.Assertion) -> T.TestTree
dimacsTests name inputs checkTest = T.testGroup name $ map mkTest inputs
  where
    mkTest input = T.testCase input $ do
      ecnf <- P.parseFile input
      case ecnf of
        Left err -> T.assertString (show err)
        Right cnf ->
          case convertCNF cnf of
            Nothing -> T.assertString "No clauses"
            Just cnf' -> do
              sol <- S.solve cnf'
              checkTest cnf sol


convertCNF :: P.CNF -> Maybe (S.CNF Int)
convertCNF cnf0 =
  S.fromSimpleList $ map fromClause (P.clauses cnf0)
  where
    fromClause c = [ fromDIMACS e
                   | e <- A.elems c
                   ]
    fromDIMACS e | e < 0 = S.N (abs e)
                 | otherwise = S.L e


expectSatisfiable :: P.CNF -> Maybe (S.Solution Int) -> T.Assertion
expectSatisfiable _  Nothing = T.assertFailure "Expected satisfying assignment"
expectSatisfiable cnf (Just sol) = mapM_ assertAtLeastOneTrue (P.clauses cnf)
  where
    assignment = S.satisfyingAssignment sol
    assertAtLeastOneTrue clause = do
      let litVal :: Int -> IO Bool
          litVal l | l < 0 = maybe msg (return . not) (lookup (abs l) assignment)
                   | otherwise = maybe msg return (lookup l assignment)
            where
              msg = error ("Expected assignment for lit " ++ show l)
      clauseValue <- mapM litVal (A.elems clause)
      T.assertBool ("Expected clause to be true: " ++ show clause) (or clauseValue)

expectUnsatisfiable :: P.CNF -> Maybe (S.Solution Int) -> T.Assertion
expectUnsatisfiable _ sol = T.assertEqual "Unexpected solution" Nothing sol

-- Setup for the binary heap tests

intComparator :: Int -> Int -> IO Bool
intComparator a b = return (a < b)

allocateUnboxedHeap :: (Int, Int) -> IO (H.Heap IOA.IOUArray Int)
allocateUnboxedHeap range = H.new range intComparator (-1)

allocateBoxedHeap :: (Int, Int) -> IO (H.Heap IOA.IOArray Int)
allocateBoxedHeap range = H.new range intComparator (-1)

-- Tests that adding a bunch of elements to the heap and removing the
-- minimum actually returns the true minimum element.
heapTests1 :: (IOA.MArray a Int IO) => String -> ((Int, Int) -> IO (H.Heap a Int)) -> T.TestTree
heapTests1 name allocator = QC.testProperty name $ MQC.monadicIO $ do
  let testRange = (0, 10000)
  nElts <- MQC.pick (QC.choose (0, 20))
  lst <- MQC.pick (QC.vectorOf nElts (QC.choose testRange))
  -- arbitrary can generate a negative number - we only want positive
  -- numbers here (including not zero, so always add at least one)
  h <- liftIO $ allocator testRange
  let minElt = minimum lst
  F.forM_ lst $ \i -> liftIO $ H.unsafeInsert h i
  mfromHeap <- liftIO $ H.takeMin h
  -- We are allowed to get Nothing (and should) if there were no
  -- elements in the heap
  case mfromHeap of
    Nothing -> MQC.assert (null lst)
    Just elt -> MQC.assert (elt == minElt)

heapTests2 :: (IOA.MArray a Int IO) => String -> ((Int, Int) -> IO (H.Heap a Int)) -> T.TestTree
heapTests2 name allocator = QC.testProperty name $ MQC.monadicIO $ do
  let testRange = (0, 10000)
  nElts <- MQC.pick (QC.choose (0, 20))
  lst <- MQC.pick (QC.vectorOf nElts (QC.choose testRange))
  -- arbitrary can generate a negative number - we only want positive
  -- numbers here (including not zero, so always add at least one)
  h <- liftIO $ allocator testRange
  F.forM_ lst $ \i -> liftIO $ H.unsafeInsert h i
  F.forM_ (L.nub (L.sort lst)) $ \expectedElt -> do
    mfromHeap <- liftIO $ H.takeMin h
    case mfromHeap of
      Nothing -> MQC.assert False
      Just elt -> MQC.assert (elt == expectedElt)
  mfromHeap <- liftIO $ H.takeMin h
  MQC.assert (mfromHeap == Nothing)


