module Syntax where

import Common

type Ty = Tm

data Tm
  = Var Ix Mode
  | Lam Name Stage Mode Icit Tm
  | App Tm Tm Stage Mode Icit
  | U Stage
  | Pi Name Stage Mode Icit Ty Ty
  | Let Name Stage Mode Ty Tm Tm
  | Meta MetaVar Marker
  | InsertedMeta MetaVar Marker [BD]
  | Lift Mode Ty
  | Quote Mode Tm
  | Splice Mode Tm
  deriving (Show)

-- Shallowly eliminate Quote and Splice constructors:

quoteS :: Mode -> Tm -> Tm
quoteS _ (Splice _ t) = t
quoteS q t = Quote q t

spliceS :: Mode -> Tm -> Tm
spliceS _ (Quote _ t) = t
spliceS q t = Splice q t
