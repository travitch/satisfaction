-- | A representation of Boolean formulas
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Satisfaction.Formula (
  Formula,
  FormulaF(..)
  ) where

import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Traversable as T

data FormulaF a t = Variable a
                  | Negation t (FormulaF a t)
                  | Conjunction t (FormulaF a t) (FormulaF a t)
                  | Disjunction t (FormulaF a t) (FormulaF a t)
                  | Implication t (FormulaF a t) (FormulaF a t)
                  | Equivalent t (FormulaF a t) (FormulaF a t)
                  | Exclusive t (FormulaF a t) (FormulaF a t)
                  deriving (Eq, Ord, Show, F.Foldable, Functor, T.Traversable)

type Formula a = FormulaF a ()

