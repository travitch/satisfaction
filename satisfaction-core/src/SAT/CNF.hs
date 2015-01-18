{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
module SAT.CNF (
  -- * Internal representation
  CNF(clauses),
  Clause,
  clauseCount,
  variableCount,
  clauseAt,
  clauseLiterals,
  clauseList,
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

clauseList :: CNF a -> [Clause]
clauseList = A.elems . clauses
{-# INLINE clauseList #-}

-- | A formula in CNF.  There will always be at least one clause.
-- Clauses may have a single variable, but may not be empty.  The
-- variable count is the number of distinct variables (ignoring
-- negations).
--
-- Clauses are simply indexed by 'Int' since that has no special
-- meaning (the number of the clause).  Variables are mapped back and
-- forth between a user-provided type @a@.
data CNF a =
  CNF { clauses :: A.Array Int Clause
      , mapping :: M.Map a Variable
      , fromInt :: A.Array Variable a
      }
  deriving (Eq, Ord, Show)

-- | Return the number of clauses in a CNF formula
clauseCount :: CNF a -> Int
clauseCount cnf = cc + 1
  where
    (0, cc) = A.bounds (clauses cnf)
{-# INLINE clauseCount #-}

-- | The number of distinct variables in the CNF formula
variableCount :: CNF a -> Int
variableCount = M.size . mapping
{-# INLINE variableCount #-}

-- | Get the clause at the given index
clauseAt :: CNF a -> Int -> Maybe Clause
clauseAt cnf ix
  | ix >= clauseCount cnf = Nothing
  | otherwise = Just $ clauses cnf A.! ix
{-# INLINE clauseAt #-}

data Lit a = L a
           | N a
           deriving (Eq, Ord, Show)

literalVariable :: Lit a -> a
literalVariable (L a) = a
literalVariable (N a) = a

-- | Take a list of clauses in CNF form and convert it to an efficient
-- internalized representation.  The conversion from a more general
-- formula language is TODO.
fromSimpleList :: (MonadPlus m, Ord a) => [[Lit a]] -> m (CNF a)
fromSimpleList klauses
  | null klauses' = mzero
  | otherwise =
      return CNF { clauses = A.array (0, nClauses - 1) arrayClauses
                 , mapping = revmap
                 , fromInt =
                   A.array fromIntBounds [ (ix, val)
                                         | (val, ix) <- M.toList revmap
                                         ]
                 }
  where
    fromIntBounds = (mkVariable 0, mkVariable (M.size revmap - 1))
    klauses' = filter (not . null) klauses
    (nClauses, revmap, arrayClauses) = foldr addClause (0, M.empty, []) (zip [0..] klauses')
    addClause (cidx, c) (nc, m, acs) =
      let (m', acVals) = foldr toArrayClause (m, []) (zip [0..] c)
          arrayClause = MkClause $ UA.array (0, length acVals - 1) acVals
      in (nc + 1, m', (cidx, arrayClause) : acs)
    toArrayClause (ix, externalLit) (m, acVals) =
      let externalVar = literalVariable externalLit
      in case M.lookup externalVar m of
           Just internalVar ->
             case externalLit of
               L _ -> (m, (ix, toPositiveLiteral internalVar) : acVals)
               N _ -> (m, (ix, toNegativeLiteral internalVar) : acVals)
           Nothing ->
             let internalVar = mkVariable (M.size m)
                 m' = M.insert externalVar internalVar m
             in toArrayClause (ix, externalLit) (m', acVals)
