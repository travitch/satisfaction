{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Main ( main ) where

import Control.Applicative
import Control.Monad ( when )
import qualified Data.Array.IArray as A
import Options.Applicative ( (<>) )
import qualified Options.Applicative as O
import qualified Language.CNF.Parse.ParseDIMACS as P
import qualified System.Exit as E

import qualified Satisfaction as S

import Prelude

data Options = Options { maxConflicts :: Maybe Int
                       , maxConflictGrowthFactor :: Maybe Double
                       , maxLearnedRatio :: Maybe Double
                       , maxLearnedAbsolute :: Maybe Int
                       , maxLearnedFactor :: Maybe Double
                       , clauseDecayFactor :: Maybe Double
                       , variableDecayFactor :: Maybe Double
                       , printStatistics :: Bool
                       , inputFile :: FilePath
                       }

solverParam :: (Read a) => String -> String -> String -> O.Parser (Maybe a)
solverParam flag metavar msg = O.optional (O.option O.auto ( O.long flag
                                                             <> O.metavar metavar
                                                             <> O.help msg ))

options :: O.Parser Options
options = Options <$> solverParam "max-conflicts" "INT" "The (initial) maximum number of conflicts before restarting.  Default: 100"
                  <*> solverParam "max-conflict-factor" "FLOAT" "The factor to grow 'max-conflicts' by after each restart.  Default: 1.5"
                  <*> solverParam "max-learned-ratio" "FLOAT" "The (initial) maximum number of learned clauses as a ratio against the number of problem clauses.  Default: 0.333"
                  <*> solverParam "max-learned-absolute" "INT" "The (initial) maximum number of learned clauses.  Exclusive with --max-learned-ratio, which is the default"
                  <*> solverParam "max-learned-factor" "FLOAT" "The factor to grow the maximum number of allowed learned clauses each restart.  Default: 1.1"
                  <*> solverParam "clause-decay-factor" "FLOAT" "The amount to decay clause activity by after each conflict.  This value should be in the range (0, 1).  Default: 0.999"
                  <*> solverParam "variable-decay-factor" "FLOAT" "The amount to decay variable activity by after each conflict.  The value should be in the range (0,1 ).  Default: 0.95"
                  <*> O.switch ( O.long "print-statistics"
                                 <> O.help "Print solver statistics before exiting" )
                  <*> O.strOption ( O.long "file"
                                  <> O.short 'f'
                                  <> O.metavar "FILE"
                                  <> O.help "An input file in DIMACS format" )


main :: IO ()
main = O.execParser opts >>= satisfy
  where
    opts = O.info (O.helper <*> options) (
      O.fullDesc
       <> O.progDesc "Solve a SAT instance"
       <> O.header "satisfaction - a SAT solver" )

satisfy :: Options -> IO ()
satisfy opts = do
  ecnf <- P.parseFile (inputFile opts)
  case ecnf of
    Left err -> print err >> E.exitFailure
    Right cnf -> do
      let mcnf' = convertCNF cnf
      case mcnf' of
        Nothing -> putStrLn "No clauses"
        Just cnf' -> do
          let config = applyOptions opts S.defaultConfig
          sol <- S.solveWith config cnf'
          case sol of
            S.Unsatisfiable {} -> putStrLn "Unsat"
            S.Satisfiable { S.solutionModel = sol' } -> print (S.satisfyingAssignment sol')
          when (printStatistics opts) $ do
            print (S.solutionStats sol)

data ParamModifier where
  ParamModifier :: forall a . Maybe a -> (a -> S.Config -> S.Config) -> ParamModifier

applyOptions :: Options -> S.Config -> S.Config
applyOptions opts cfg0 = foldr applyOption cfg0 modifiers
  where
    modifiers = [ ParamModifier (maxConflicts opts) S.setMaxConflicts
                , ParamModifier (maxConflictGrowthFactor opts) S.setMaxConflictGrowthFactor
                , ParamModifier (maxLearnedRatio opts) S.setMaxLearnedClausesRatio
                , ParamModifier (maxLearnedAbsolute opts) S.setMaxLearnedClausesAbsolute
                , ParamModifier (maxLearnedFactor opts) S.setMaxLearnedClauseGrowthFactor
                , ParamModifier (clauseDecayFactor opts) S.setClauseActivityDecayFactor
                , ParamModifier (variableDecayFactor opts) S.setVariableActivityDecayFactor
                ]

    applyOption (ParamModifier Nothing _) o = o
    applyOption (ParamModifier (Just v) f) o = f v o

convertCNF :: P.CNF -> Maybe (S.CNF Int)
convertCNF cnf0 =
  S.fromSimpleList $ map fromClause (P.clauses cnf0)
  where
    fromClause c = [ fromDIMACS e
                   | e <- A.elems c
                   ]
    fromDIMACS e | e < 0 = S.N (abs e)
                 | otherwise = S.L e
