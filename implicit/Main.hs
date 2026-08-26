module Main where

import Common
import Control.Exception
import Cxt
import Elaboration
import Errors
import Evaluation
import Extraction (extract)
import Metacontext
import Parser
import Staging (quoteO, stage)
import qualified Presyntax as P
import Pretty
import System.Environment
import System.Exit

--------------------------------------------------------------------------------

helpMsg =
  unlines
    [ "usage: comptt-impl [--help|elab|nf|type]",
      "  --help : display this message",
      "  elab   : read & elaborate expression from stdin",
      "  stage  : read & typecheck expression from stdin, print its staged form",
      "  nf     : read & typecheck expression from stdin, print its normal form and type",
      "  type   : read & typecheck expression from stdin, print its type"
    ]

showHelp = putStrLn helpMsg >> exitFailure

mainWith :: IO [String] -> IO (P.Tm, String) -> IO ()
mainWith getOpt getRaw = do
  (t, file) <- getRaw
  let elab m = do
        inferIn (emptyCxt (initialPos file)) SObj m t
          `catch` \e -> (displayError file e >> exitFailure)

  let staged m = do
        (t, _) <- elab m
        stage (initialPos file) t
          `catch` \e -> (displayError file e >> exitFailure)

  let parseMode "0" = pure Zero
      parseMode "" = pure Omega
      parseMode _ = showHelp

  reset
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ['n' : 'f' : optMode] -> do
      q <- parseMode optMode
      (t, a) <- elab q
      putStrLn $ showTm0 $ nf (getMarker q) [] t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote 0 a
    ['t' : 'y' : 'p' : 'e' : optMode] -> do
      q <- parseMode optMode
      (t, a) <- elab q
      putStrLn $ showTm0 $ quote 0 a
    ['e' : 'l' : 'a' : 'b' : optMode] -> do
      q <- parseMode optMode
      (t, a) <- elab q
      displayMetas
      putStrLn $ showTm0 t
    ["ex"] -> do
      t <- staged Omega
      putStrLn $ showCode0 (extract t)
    ["stage"] -> do
      t <- staged Omega
      putStrLn $ showTm0 (quoteO 0 t)
    _ -> showHelp

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
