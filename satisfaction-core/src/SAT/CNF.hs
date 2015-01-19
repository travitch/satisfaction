{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module SAT.CNF (
  -- * Internal representation
  CNF,
  Clause,
  clauseCount,
  variableCount,
  clauseAt,
  clauseLiterals,
  clauseLiteral,
  clauseRange,
  clauseList,
  clauseArray,
  mapSolution,
  -- * External interface
  Lit(..),
  fromSimpleList
  ) where

import Control.Monad
import qualified Data.Array.IArray as A
import qualified Data.Array.Unboxed as UA
import qualified Data.Map as M

import SAT.Literal

newtype Clause = MkClause { clauseAsArray :: UA.UArray Int Literal }
               deriving (Eq, Ord, Show)

-- | Return the 'Literal's in a 'Clause' as a list.
--
-- Obviously, this should not be used in a tight inner loop.
clauseLiterals :: Clause -> [Literal]
clauseLiterals = A.elems . clauseAsArray
{-# INLINE clauseLiterals #-}

clauseLiteral :: Clause -> Int -> Literal
clauseLiteral c i = clauseAsArray c A.! i
{-# INLINE clauseLiteral #-}

clauseRange :: Clause -> (Int, Int)
clauseRange = A.bounds . clauseAsArray
{-# INLINE clauseRange #-}

clauseList :: CNF a -> [Clause]
clauseList = A.elems . cnfClauses
{-# INLINE clauseList #-}

clauseArray :: CNF a -> A.Array Int Clause
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
  CNF { cnfClauses :: A.Array Int Clause
      , cnfToVariable :: M.Map a Variable
      , cnfFromVariable :: A.Array Variable a
      }
  deriving (Eq, Ord, Show)

mapSolution :: (A.IArray array Value) => CNF a -> array Variable Value -> [(a, Bool)]
mapSolution cnf a = [ (elt, toBool (a A.! intvar))
                    | (elt, intvar) <- M.toList (cnfToVariable cnf)
                    ]
  where
    toBool = (==liftedTrue)

-- | Return the number of clauses in a CNF formula
clauseCount :: CNF a -> Int
clauseCount cnf = cc + 1
  where
    (0, cc) = A.bounds (cnfClauses cnf)
{-# INLINE clauseCount #-}

-- | The number of distinct variables in the CNF formula
variableCount :: CNF a -> Int
variableCount = M.size . cnfToVariable
{-# INLINE variableCount #-}

-- | Get the clause at the given index
clauseAt :: CNF a -> Int -> Maybe Clause
clauseAt cnf ix
  | ix >= clauseCount cnf = Nothing
  | otherwise = Just $ cnfClauses cnf A.! ix
{-# INLINE clauseAt #-}

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
      return CNF { cnfClauses = A.array (0, length arrayClauses - 1) arrayClauses
                 , cnfToVariable = toVar
                 , cnfFromVariable =
                   A.array bounds [ (ix, val)
                                  | (val, ix) <- M.toList toVar
                                  ]
                 }
  where
    bounds = (firstVariable, highestVariable)
    -- @highestVar@ will always be valid because we have no null
    -- clauses and at least one clause, hence at least one variable.
    seed = ((firstVariable, firstVariable), M.empty, [])
    ((_, highestVariable), toVar, arrayClauses) = foldr addClause seed (zip [0..] klauses)
    addClause (clauseIndex, clause) (vars, m, clauses) =
      let (vars', m', arrayClauseElts) = foldr toArrayClause (vars, m, []) (zip [0..] clause)
          arrayClause = MkClause $ UA.array (0, length arrayClauseElts - 1) arrayClauseElts
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
