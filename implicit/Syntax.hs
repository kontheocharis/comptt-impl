module Syntax where

import Common

type Ty = Tm

data Tm
  = Var Ix Mode
  | Lam Name Mode Icit Tm
  | App Tm Tm Mode Icit
  | U
  | Pi Name Mode Icit Ty Ty
  | Let Name Mode Ty Tm Tm
  | Meta MetaVar Marker
  | InsertedMeta MetaVar Marker [BD]
  deriving (Show)
