module Presyntax where

import Common

data Tm
  = Var Name -- x
  | Lam Name (Either Name Icit) Tm -- \x. t | \{x}. t | \{x = y}. t
  | App Tm Tm (Either Name Icit) -- t u  | t {u} | t {x = u}
  | U -- U
  | Pi Name Mode Icit Tm Tm -- (i x : A) -> B | {i x : A} -> B
  | Let Name Mode Tm Tm Tm -- let i x : A = t; u
  | SrcPos SourcePos Tm -- source position for error reporting
  | Hole -- _
  deriving (Show)
