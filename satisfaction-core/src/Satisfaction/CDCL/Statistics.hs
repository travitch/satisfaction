module Satisfaction.CDCL.Statistics (
  Statistics(..),
  extractStatistics
  ) where

import qualified Data.Ref.Prim as P
import Satisfaction.CDCL.Monad

-- | Solver statistics
data Statistics =
  Statistics { sTotalConflicts :: Int
             , sRestartCount :: Int
             , sGroundLevels :: Int
             , sDecisionCount :: Int
             , sPropagations :: Int
             , sLearnedCleanup :: Int
             }
  deriving (Show)

-- | Read the current statistics out of the state
extractStatistics :: Solver Statistics
extractStatistics = do
  e <- ask
  totalConflicts <- P.readRef (eTotalConflicts e)
  curConflicts <- P.readRef (eCurrentConflicts e)
  restartCount <- P.readRef (eRestartCount e)
  groundLevels <- P.readRef (eAtGround e)
  decisionCount <- P.readRef (eDecisionCount e)
  props <- P.readRef (ePropagations e)
  cleaned <- P.readRef (eLearnedCleanup e)
  return Statistics { sTotalConflicts = totalConflicts + curConflicts
                    , sRestartCount = restartCount
                    , sGroundLevels = groundLevels
                    , sDecisionCount = decisionCount
                    , sPropagations = props
                    , sLearnedCleanup = cleaned
                    }
