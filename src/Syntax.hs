module Syntax where

import Common

-- nbe chat going to hate this

type Ty = Tm

type Rep = Tm

type Pol = Tm

data Tm
  = Var Ix Mode
  | Lam Name Stage Mode Icit Tm
  | App Tm Tm Stage Mode Icit
  | UMeta
  | UObj Pol Rep
  | Pi Name Stage Mode Icit Rep Ty Ty
  | Producer Ty
  | Ret Tm
  | Let Name Stage Mode Ty Tm Tm
  | Meta MetaVar Marker
  | InsertedMeta MetaVar Marker [BD]
  | Lift Mode Ty
  | Quote Mode Tm
  | Splice Mode Tm
  | PolU
  | Pol Polarity
  | RepU Pol
  | Rep (RepF Pol Rep)
  deriving (Show)

unitRep :: Rep
unitRep = Rep (RUnit (Pol Pos))

quoteS :: Mode -> Tm -> Tm
quoteS _ (Splice _ t) = t
quoteS q t = Quote q t

spliceS :: Mode -> Tm -> Tm
spliceS _ (Quote _ t) = t
spliceS q t = Splice q t
