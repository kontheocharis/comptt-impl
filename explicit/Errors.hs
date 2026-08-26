module Errors where

import Common
import Control.Exception
import Cxt
import Syntax
import Text.Printf

--------------------------------------------------------------------------------

data UnifyError
  = Escaping
  | Occurs
  | UnifyError
  | EscapingMarker
  | InversionNonVariables
  | InversionNonLinear
  deriving (Show, Exception)

data ElabError
  = NameNotInScope Name
  | CantUnify Tm Tm UnifyError
  | InferNamedLam
  | NoNamedImplicitArg Name
  | IcitMismatch Icit Icit
  | InsufficientMode
  deriving (Show, Exception)

data ExtractError
  = CannotExtractMeta
  deriving (Show, Exception)

data SomeError = ExtractError ExtractError | ElabError Cxt ElabError
  deriving (Show, Exception)

data Error = Error SourcePos SomeError
  deriving (Show, Exception)

displayError :: String -> Error -> IO ()
displayError file (Error ps e) = do
  let SourcePos path (unPos -> linum) (unPos -> colnum) = ps
      lnum = show linum
      lpad = map (const ' ') lnum
      msg = case e of
        ExtractError e' -> case e' of
          CannotExtractMeta ->
            "Cannot extract term with unsolved meta-variables"
        ElabError cxt e' -> case e' of
          NameNotInScope x ->
            "Name not in scope: " ++ x
          CantUnify t t' ue ->
            ( "Cannot unify expected type\n\n"
                ++ "  "
                ++ showTm cxt t
                ++ "\n\n"
                ++ "with inferred type\n\n"
                ++ "  "
                ++ showTm cxt t'
                ++ case ue of
                  UnifyError -> ""
                  Escaping -> "\n\n(escaping variable)"
                  Occurs -> "\n\n(occurs check failed)"
                  EscapingMarker -> "\n\n(escaping erasure marker)"
                  InversionNonVariables -> "\n\n(spine inversion failed due to non-variable)"
                  InversionNonLinear -> "\n\n(spine inversion failed due to non-linear use of variables)"
            )
          InferNamedLam ->
            "Cannot infer type for lambda with named argument"
          NoNamedImplicitArg name ->
            "No named implicit argument with name " ++ name
          IcitMismatch i i' ->
            printf
              ("Function icitness mismatch: expected %s, got %s.")
              (show i)
              (show i')
          InsufficientMode ->
            "Term is valid in mode 0 but need mode ω"

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n" lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg
