module Main ( main ) where

import Control.Applicative
import qualified Data.Array.IArray as A
import Options.Applicative ( (<>) )
import qualified Options.Applicative as O
import qualified Language.CNF.Parse.ParseDIMACS as P
import qualified System.Exit as E

import qualified SAT.Solver as S

data Options = Options { inputFile :: FilePath }

options :: O.Parser Options
options = Options <$> O.strOption ( O.long "file"
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
          sol <- S.solve cnf'
          case sol of
            Nothing -> putStrLn "Unsat"
            Just sol' -> print (S.satisfyingAssignment sol')

convertCNF :: P.CNF -> Maybe (S.CNF Int)
convertCNF cnf0 =
  S.fromSimpleList $ map fromClause (P.clauses cnf0)
  where
    fromClause c = [ fromDIMACS e
                   | e <- A.elems c
                   ]
    fromDIMACS e | e < 0 = S.N (abs e)
                 | otherwise = S.L e
