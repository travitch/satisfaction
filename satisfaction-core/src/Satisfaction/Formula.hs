-- | A representation of Boolean formulas
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Satisfaction.Formula (
  -- * Internal CNF representation
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
  cnfMapVariable,
  -- * External CNF interface
  Lit(..),
  fromSimpleList,
  -- * General formula interface
  Formula,
  LFormula,
  variable,
  negation,
  conjunction,
  disjunction,
  implication,
  equivalent,
  exclusive,
  T.toCNF
  ) where

import Control.Monad ( MonadPlus(..) )
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified Data.Array.Prim as PA
import qualified Data.Array.Prim.Generic as GA
import qualified Data.Array.Prim.Unboxed as PUA

import Satisfaction.Formula.Internal
import qualified Satisfaction.Formula.Literal as L
import qualified Satisfaction.Formula.Tseitin as T

variable :: a -> Formula a
variable = Variable ()

negation :: Formula a -> Formula a
negation = Negation ()

conjunction :: Formula a -> Formula a -> Formula a
conjunction = Binary Conjunction ()

disjunction :: Formula a -> Formula a -> Formula a
disjunction = Binary Disjunction ()

implication :: Formula a -> Formula a -> Formula a
implication = Binary Implication ()

equivalent :: Formula a -> Formula a -> Formula a
equivalent = Binary Equivalent ()

exclusive :: Formula a -> Formula a -> Formula a
exclusive = Binary Exclusive ()


-- CNF

-- | Return 'True' if the clause has only a single literal
clauseIsSingleton :: Clause -> Bool
clauseIsSingleton c = clauseSize c == 1
{-# INLINE clauseIsSingleton #-}

-- | Return the 'Literal's in a 'Clause' as a list.
--
-- Obviously, this should not be used in a tight inner loop.
clauseLiterals :: Clause -> [L.Literal]
clauseLiterals = PUA.elems . clauseAsArray
{-# INLINE clauseLiterals #-}

clauseLiteral :: Clause -> Int -> L.Literal
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


cnfMapVariable :: (Ord a) => CNF a -> a -> Maybe L.Variable
cnfMapVariable cnf a = M.lookup a (cnfToVariable cnf)

mapSolution :: (GA.PrimArray array L.Value) => CNF a -> array L.Variable L.Value -> [(a, Bool)]
mapSolution cnf a = [ (elt, toBool (a GA.! intvar))
                    | (elt, intvar) <- M.toList (cnfToVariable cnf)
                    ]
  where
    toBool = (==L.liftedTrue)

-- | Return the number of clauses in a CNF formula
clauseCount :: CNF a -> Int
clauseCount = PA.size . cnfClauses
{-# INLINE clauseCount #-}

-- | The number of distinct variables in the CNF formula
variableCount :: CNF a -> Int
variableCount = M.size . cnfToVariable
{-# INLINE variableCount #-}

variableRange :: CNF a -> (L.Variable, L.Variable)
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
                   M.fromList [ (ix, val)
                              | (val, ix) <- M.toList toVar
                              ]
                 , cnfVarRange = (L.firstVariable, lastVar)
                 }
  where
    seed = ((L.firstVariable, L.firstVariable), M.empty, [])
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
               L _ -> (vars, m, (ix, L.toPositiveLiteral internalVar) : elts)
               N _ -> (vars, m, (ix, L.toNegativeLiteral internalVar) : elts)
           Nothing ->
             -- If we haven't already mapped this external variable to
             -- an internal variable, perform the mapping (updating
             -- @m@) and then try again.
             let m' = M.insert externalVar varSrc m
             in toArrayClause litRef ((L.nextVariable varSrc, varSrc), m', elts)

unique :: (Ord a) => [a] -> [a]
unique = S.toList . S.fromList


{- Note [Tseitin]

This transformation converts a general boolean formula to CNF with
only a linear space overhead.

It first assigns a fresh variable to each sub-formula, then transforms
each sub-formula (except for variables) according to some simple
rules.  Finally, it conjoins all of the transformed fragments into a
single large formula (which is in CNF).

For example, consider: -(x_1 <-> x_2)

We can assign y_1 to the negation and y_2 to the bi-implication.

We'll rewrite the negation to:

(-y_1 OR -y_2) AND (y_1 or y_2)

We'll rewrite the negation to:

(-y_2 OR -x_1 OR x_2) AND (-y_2 OR -x_2 OR x_1) AND (y_2 OR -x_1 OR -x_2) AND (y_2 OR x_1 OR x_2)

Note that we have CNF when we combine these two.

-}
