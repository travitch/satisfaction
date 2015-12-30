{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# OPTIONS_HADDOCK not-home #-}
-- | This module contains internal definitions relating to formulas
--
-- Other modules require these, but the implementations are not really
-- meant to be exposed.  Use at your own risk.
module Satisfaction.Formula.Internal (
  -- * General formulas
  FormulaF(..),
  Operator(..),
  Formula,
  LFormula,
  -- * CNF
  CNF(..),
  -- * Clauses
  Clause(..),
  clause
  ) where

import GHC.Generics ( Generic )

import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Traversable as T

import qualified Data.Array.Prim as PA
import qualified Data.Array.Prim.Unboxed as PUA

import qualified Satisfaction.Formula.Literal as L

data Operator = Conjunction
              | Disjunction
              | Implication
              | Equivalent
              | Exclusive
              deriving (Eq, Ord, Show, Generic)

-- | The underlying 'Formula' AST type.  The 't' parameter holds
-- labels in the 'LFormula', and is unit in the user-facing version.
--
-- There are two so that users can build up formulas purely without
-- having to allocate IDs.  It would be nice to expose a monadic
-- interface that allowed for safe ID allocation to sub-formulas on
-- the fly.
data FormulaF a t = Variable t a
                  | Negation t (FormulaF a t)
                  | Binary Operator t (FormulaF a t) (FormulaF a t)
                  deriving (Eq, Ord, Show, F.Foldable, Functor, T.Traversable, Generic)

-- | An arbitrary boolean formula
type Formula a = FormulaF a ()

type LFormula a = FormulaF a L.Variable

newtype Clause = MkClause { clauseAsArray :: PUA.Array Int L.Literal }
               deriving (Eq, Ord, Show)

clause :: L.Literal -> [L.Literal] -> Clause
clause l ls = MkClause (PUA.fromList (l : ls))
{-# INLINE clause #-}

-- | A formula in CNF.  There will always be at least one clause.
-- Clauses may have a single variable, but may not be empty.  The
-- variable count is the number of distinct variables (ignoring
-- negations).
--
-- Clauses are simply indexed by 'Int' since that has no special
-- meaning (the number of the clause).  Variables are mapped back and
-- forth between a user-provided type @a@.
--
-- See Note [Representation]
data CNF a =
  CNF { cnfClauses :: PA.Array Int Clause
      , cnfToVariable :: M.Map a L.Variable
      , cnfFromVariable :: M.Map L.Variable a
      , cnfVarRange :: (L.Variable, L.Variable)
      }
  deriving (Eq, Ord, Show)

{- Note [Representation]

'cnfFromVariable' used to be represented as an @Array L.Variable a@.
This is nice and compact, but made it difficult to construct the array
in the conversion to CNF from arbitrary formulas; in that case, there
are variables that do not correspond to problem variables, so there is
no associated 'a'.  The Map representation makes this simple to deal
with.

To go back to an Array representation, we would have to pre-allocate
'L.Variable's for each problem variable and construct the array
mapping early.  Then non-problem variables would all be larger.

-}
