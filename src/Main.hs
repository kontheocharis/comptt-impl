module Main where

import Common
import Control.Exception
import Control.Monad (foldM)
import Cxt
import Elaboration
import Errors
import Evaluation
import Extraction (extract)
import Metacontext
import Parser
import qualified Presyntax as P
import Pretty
import Staging (quoteO, stage)
import System.Environment
import System.Exit

data Command = Elab | Nf | Type | Staged | Extracted deriving (Eq)

data Options = Options
  { optCommand :: Command,
    optStage :: Stage,
    optMode :: Mode
  }

commands :: [(String, Command)]
commands =
  [ ("elab", Elab),
    ("nf", Nf),
    ("type", Type),
    ("stage", Staged),
    ("ex", Extracted)
  ]

helpMsg :: String
helpMsg =
  unlines
    [ "usage: comptt <command> [--meta] [--erased]",
      "",
      "commands:",
      "  elab    elaborate stdin, printing the metacontext and the result",
      "  nf      print the normal form of stdin, and its type",
      "  type    print the type of stdin",
      "  stage   print the staged object stdin",
      "  ex      print the extracted object stdin",
      "",
      "options:",
      "  --meta    elaborate at the meta stage",
      "  --erased  elaborate in mode 0",
      "  --help    show this message"
    ]

parseArgs :: [String] -> Either String Options
parseArgs [] = Left "no command given"
parseArgs (c : flags) = do
  cmd <- maybe (Left ("unknown command: " ++ c)) Right (lookup c commands)
  foldM flag (Options cmd SObj Omega) flags >>= validate
  where
    flag opts = \case
      "--meta" -> Right opts {optStage = SMeta}
      "--erased" -> Right opts {optMode = Zero}
      f -> Left ("unknown option: " ++ f)

    validate opts
      | optStage opts == SMeta && optMode opts == Zero =
          Left "the meta stage has no erased mode"
      | optStage opts == SMeta && optCommand opts `elem` [Staged, Extracted] =
          Left "staging needs an object-stage term"
      | otherwise = Right opts

run :: Options -> (P.Tm, String) -> IO ()
run opts (t, file) = do
  reset
  let die :: Error -> IO a
      die e = displayError file e >> exitFailure
      elab = inferIn (emptyCxt (initialPos file)) (optStage opts) (optMode opts) t `catch` die
      staged = do
        (t, _) <- elab
        stage (initialPos file) t `catch` die
  case optCommand opts of
    Elab -> do
      (t, _) <- elab
      displayMetas
      putStrLn $ showTm0 t
    Nf -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ nf [] t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote 0 a
    Type -> do
      (_, a) <- elab
      putStrLn $ showTm0 $ quote 0 a
    Staged ->
      putStrLn . showTm0 . quoteO 0 =<< staged
    Extracted ->
      putStrLn . showCode0 . extract =<< staged

mainWith :: IO [String] -> IO (P.Tm, String) -> IO ()
mainWith getOpt getRaw =
  getOpt >>= \case
    args | "--help" `elem` args -> putStrLn helpMsg
    args -> case parseArgs args of
      Left err -> do
        putStrLn ("comptt: " ++ err)
        putStrLn ""
        putStrLn helpMsg
        exitFailure
      Right opts -> run opts =<< getRaw

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: [String] -> String -> IO ()
main' args src = mainWith (pure args) ((,src) <$> parseString src)
