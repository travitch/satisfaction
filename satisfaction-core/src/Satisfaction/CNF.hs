{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Satisfaction.CNF (
  -- * Internal representation
  CNF,
  Clause,
  clause,
  clauseCount,
  variableCount,
  variableRange,
  clauseAt,
  clauseLiterals,
  clauseLiteral,
  clauseSize,
  clauseIsSingleton,
  clauseList,
  clauseArray,
  mapSolution,
  -- * External interface
  Lit(..),
  fromSimpleList
  ) where

import Control.Monad
import qualified Data.Array.Prim as PA
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed as PUA
import qualified Data.Map as M
import qualified Data.Set as S

import Satisfaction.Internal.Literal

newtype Clause = MkClause { clauseAsArray :: PUA.Array Int Literal }
               deriving (Eq, Ord, Show)

clause :: Literal -> [Literal] -> Clause
clause l ls = MkClause (PUA.fromList (l : ls))
{-# INLINE clause #-}

-- | Return 'True' if the clause has only a single literal
clauseIsSingleton :: Clause -> Bool
clauseIsSingleton c = clauseSize c == 1
{-# INLINE clauseIsSingleton #-}

-- | Return the 'Literal's in a 'Clause' as a list.
--
-- Obviously, this should not be used in a tight inner loop.
clauseLiterals :: Clause -> [Literal]
clauseLiterals = PUA.elems . clauseAsArray
{-# INLINE clauseLiterals #-}

clauseLiteral :: Clause -> Int -> Literal
clauseLiteral c i = clauseAsArray c PUA.! i
{-# INLINE clauseLiteral #-}

clauseSize :: Clause -> Int
clauseSize = GA.plength . clauseAsArray
{-# INLINE clauseSize #-}

clauseList :: CNF a -> [Clause]
clauseList = PA.elems . cnfClauses
{-# INLINE clauseList #-}

clauseArray :: CNF a -> PA.Array Int Clause
clauseArray = cnfClauses
{-# INLINE clauseArray #-}

-- | A formula in CNF.  There will always be at least one clause.
-- Clauses may have a single variable, but may not be empty.  The
-- variable count is the number of distinct variables (ignoring
-- negations).
--
-- Clauses are simply indexed by 'Int' since that has no special
-- meaning (the number of the clause).  Variables are mapped back and
-- forth between a user-provided type @a@.
data CNF a =
  CNF { cnfClauses :: PA.Array Int Clause
      , cnfToVariable :: M.Map a Variable
      , cnfFromVariable :: PA.Array Variable a
      , cnfVarRange :: (Variable, Variable)
      }
  deriving (Eq, Ord, Show)

mapSolution :: (GA.PrimArray array Value) => CNF a -> array Variable Value -> [(a, Bool)]
mapSolution cnf a = [ (elt, toBool (a GA.! intvar))
                    | (elt, intvar) <- M.toList (cnfToVariable cnf)
                    ]
  where
    toBool = (==liftedTrue)

-- | Return the number of clauses in a CNF formula
clauseCount :: CNF a -> Int
clauseCount = PA.size . cnfClauses
{-# INLINE clauseCount #-}

-- | The number of distinct variables in the CNF formula
variableCount :: CNF a -> Int
variableCount = M.size . cnfToVariable
{-# INLINE variableCount #-}

variableRange :: CNF a -> (Variable, Variable)
variableRange = cnfVarRange

-- | Get the clause at the given index
clauseAt :: CNF a -> Int -> Maybe Clause
clauseAt cnf ix
  | ix >= clauseCount cnf = Nothing
  | otherwise = Just $ cnfClauses cnf GA.! ix
{-# INLINE clauseAt #-}

-- | A literal is a positive or negative occurrence of a variable.
--
-- This representation allows the underlying variable to be of any
-- type.
data Lit a = L a -- ^ A positive literal
           | N a -- ^ A negative literal
           deriving (Eq, Ord, Show)

literalVariable :: Lit a -> a
literalVariable (L a) = a
literalVariable (N a) = a

-- | Take a list of clauses in CNF form and convert it to an efficient
-- internalized representation.  The conversion from a more general
-- formula language is TODO.
--
-- Empty clauses are discarded.  This function will fail (i.e., return
-- 'mzero') if there are no non-empty clauses provided.
fromSimpleList :: (MonadPlus m, Ord a) => [[Lit a]] -> m (CNF a)
fromSimpleList (filter (not . null) -> klauses)
  | null klauses = mzero
  | otherwise =
      return CNF { cnfClauses = PA.array arrayClauses
                 , cnfToVariable = toVar
                 , cnfFromVariable =
                   PA.array [ (ix, val)
                            | (val, ix) <- M.toList toVar
                            ]
                 , cnfVarRange = (firstVariable, lastVar)
                 }
  where
    seed = ((firstVariable, firstVariable), M.empty, [])
    ((_, lastVar), toVar, arrayClauses) = foldr addClause seed (zip [0..] klauses)
    addClause (clauseIndex, cl) (vars, m, clauses) =
      let (vars', m', arrayClauseElts) = foldr toArrayClause (vars, m, []) (zip [0 :: Int ..] cl)
          arrayClause = MkClause $ PUA.fromList (unique (map snd arrayClauseElts))
      in (vars', m', (clauseIndex, arrayClause) : clauses)
    toArrayClause litRef@(ix, externalLit) (vars@(varSrc, _), m, elts) =
      let externalVar = literalVariable externalLit
      in case M.lookup externalVar m of
           Just internalVar ->
             case externalLit of
               L _ -> (vars, m, (ix, toPositiveLiteral internalVar) : elts)
               N _ -> (vars, m, (ix, toNegativeLiteral internalVar) : elts)
           Nothing ->
             -- If we haven't already mapped this external variable to
             -- an internal variable, perform the mapping (updating
             -- @m@) and then try again.
             let m' = M.insert externalVar varSrc m
             in toArrayClause litRef ((nextVariable varSrc, varSrc), m', elts)

unique :: (Ord a) => [a] -> [a]
unique = S.toList . S.fromList
