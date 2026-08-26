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
  | Lift Ty
  | Quote Tm
  | Splice Tm
  deriving (Show)

-- Shallowly eliminate Quote and Splice constructors:

quoteS :: Tm -> Tm
quoteS (Splice t) = t
quoteS t = Quote t

spliceS :: Tm -> Tm
spliceS (Quote t) = t
spliceS t = Splice t
