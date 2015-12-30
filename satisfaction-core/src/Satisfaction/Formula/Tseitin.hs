-- | This module implements Tseitin's transformation to convert
-- arbitrary boolean 'Formula's into CNF.
module Satisfaction.Formula.Tseitin (
  toCNF
  ) where

import Control.Monad.ST
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import Data.Monoid
import qualified Data.Sequence as Seq
import qualified Data.Traversable as T

import Prelude

import qualified Data.Array.Prim as PA
import qualified Data.Ref.Prim as P

import Satisfaction.Formula.Internal
import qualified Satisfaction.Formula.Literal as L

-- | Convert a formula to CNF using Tseitin's transformation
--
-- See Note [Tseitin] for details
toCNF :: (Ord a) => Formula a -> CNF a
toCNF f0 = runST $ do
  r <- P.newRef emptyConversionState
  convertSubformula r labeledFormula

  -- We have to create a special clause that just references the label
  -- of the root of the formula to force the whole thing to be true.
  rootVar <- formulaVariable r labeledFormula
  let rootClause = clause (L.toPositiveLiteral rootVar) []
  s <- P.readRef r

  -- Note that we cannot support empty formulas (because 'CNF' tracks
  -- its variable range), but 'Formula' cannot represent empty
  -- formulas, so it is fine.
  return $! CNF { cnfClauses = PA.fromList (rootClause : F.toList (csClauses s))
                , cnfToVariable = csProblemVarMap s
                , cnfFromVariable = csProblemVarInvMap s
                , cnfVarRange = (L.firstVariable, highestVar)
                }
  where
    (labeledFormula, highestVar) = labelSubformulas f0

-- | Assign a unique label to each sub-formula that is not a bare
-- variable reference.
--
-- Returns the labeled formula and the highest variable allocated.
labelSubformulas :: Formula a -> (LFormula a, L.Variable)
labelSubformulas f0 = runST $ do
  r <- P.newRef (L.firstVariable, L.firstVariable)
  f1 <- T.traverse (applyLabels r) f0
  (_, highestVar) <- P.readRef r
  return (f1, highestVar)
  where
    applyLabels r () = do
      (lbl, _) <- P.readRef r
      P.writeRef r (L.nextVariable lbl, lbl)
      return lbl

type CSRef s a = P.Ref (ST s) (ConversionState a)

-- | Perform the actual Tseitin conversion.
--
-- Variables don't really appear directly.  They will simply be
-- referenced from operators.
convertSubformula :: (Ord a) => CSRef s a -> LFormula a -> ST s ()
convertSubformula r f =
  case f of
    Variable {} -> return ()
    Negation _ f' -> do
      -- The representative for -x
      repr <- formulaVariable r f
      -- The variable for x
      v' <- formulaVariable r f'
      -- This produces two clauses: (repr OR x) and (-repr OR -x)
      let c1 = clause (L.toPositiveLiteral repr) [L.toPositiveLiteral v']
          c2 = clause (L.toNegativeLiteral repr) [L.toNegativeLiteral v']
      P.modifyRef' r (prependClauses [c1, c2])
    Binary op _ f1 f2 -> do
      repr <- formulaVariable r f
      v1 <- formulaVariable r f1
      v2 <- formulaVariable r f2
      case op of
        Conjunction -> do
          let c1 = clause (L.toNegativeLiteral repr) [L.toPositiveLiteral v1]
              c2 = clause (L.toNegativeLiteral repr) [L.toPositiveLiteral v2]
              c3 = clause (L.toPositiveLiteral repr) [L.toNegativeLiteral v1, L.toNegativeLiteral v2]
          P.modifyRef' r (prependClauses [c1, c2, c3])
        Disjunction -> do
          let c1 = clause (L.toPositiveLiteral repr) [L.toNegativeLiteral v1]
              c2 = clause (L.toPositiveLiteral repr) [L.toNegativeLiteral v2]
              c3 = clause (L.toNegativeLiteral repr) [L.toPositiveLiteral v1, L.toPositiveLiteral v2]
          P.modifyRef' r (prependClauses [c1, c2, c3])
        Implication -> do
          let c1 = clause (L.toPositiveLiteral repr) [L.toPositiveLiteral v1]
              c2 = clause (L.toPositiveLiteral repr) [L.toNegativeLiteral v2]
              c3 = clause (L.toNegativeLiteral repr) [L.toPositiveLiteral v2, L.toNegativeLiteral v1]
          P.modifyRef' r (prependClauses [c1, c2, c3])
        Exclusive -> do
          let c1 = clause (L.toPositiveLiteral repr) [L.toNegativeLiteral v1, L.toPositiveLiteral v2]
              c2 = clause (L.toPositiveLiteral repr) [L.toPositiveLiteral v1, L.toNegativeLiteral v2]
              c3 = clause (L.toNegativeLiteral repr) [L.toPositiveLiteral v1, L.toPositiveLiteral v2]
              c4 = clause (L.toNegativeLiteral repr) [L.toNegativeLiteral v1, L.toNegativeLiteral v2]
          P.modifyRef' r (prependClauses [c1, c2, c3, c4])
        Equivalent -> do
          let c1 = clause (L.toNegativeLiteral repr) [L.toPositiveLiteral v1, L.toNegativeLiteral v2]
              c2 = clause (L.toNegativeLiteral repr) [L.toNegativeLiteral v1, L.toPositiveLiteral v2]
              c3 = clause (L.toPositiveLiteral repr) [L.toNegativeLiteral v1, L.toNegativeLiteral v2]
              c4 = clause (L.toPositiveLiteral repr) [L.toPositiveLiteral v1, L.toPositiveLiteral v2]
          P.modifyRef' r (prependClauses [c1, c2, c3, c4])

prependClauses :: [Clause] -> ConversionState a -> ConversionState a
prependClauses cs s = s { csClauses = Seq.fromList cs <> csClauses s }

data ConversionState a =
  CS { csProblemVarMap :: !(M.Map a L.Variable)
     -- ^ A map from problem variables to their allocated variables
     , csProblemVarInvMap :: !(M.Map L.Variable a)
     -- ^ The inverse mapping, required to construct a CNF
     , csClauses :: !(Seq.Seq Clause)
     -- ^ All of the clauses we have constructed
     }

emptyConversionState :: ConversionState a
emptyConversionState = CS { csProblemVarMap = M.empty
                          , csProblemVarInvMap = M.empty
                          , csClauses = Seq.empty
                          }

-- | Pull out the 'L.Variable' label for the given sub-formula.
--
-- For  each sub-formula  processed, it  records appropriate  mappings
-- from problem variable to 'L.Variable'.
formulaVariable :: (Ord a) => P.Ref (ST s) (ConversionState a) -> LFormula a -> ST s L.Variable
formulaVariable r f = do
  s <- P.readRef r
  case f of
    Variable lbl v ->
      case M.member v (csProblemVarMap s) of
        True -> return lbl
        False -> do
          let s' = s { csProblemVarMap = M.insert v lbl (csProblemVarMap s)
                     , csProblemVarInvMap = M.insert lbl v (csProblemVarInvMap s)
                     }
          P.writeRef r s'
          return lbl
    Negation lbl _ -> return lbl
    Binary _ lbl _ _ -> return lbl

