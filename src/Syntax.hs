module Syntax where

import Common

-- nbe chat going to hate this

type Ty = Tm

type Rep = Tm

type Pol = Tm

data Tm
  = Var Ix
  | LamObj Name Mode Icit Ty Tm
  | LamMeta Name Icit Ty Tm
  | AppObj Tm Tm Mode Icit
  | AppMeta Tm Tm Icit
  | UMeta
  | UObj Pol Rep
  | PiObj Name Mode Icit Rep Ty Ty
  | PiMeta Name Icit Ty Ty
  | Producer Ty
  | Ret Tm
  | Let Name Stage Mode Ty Tm Tm
  | Meta MetaVar Phase
  | InsertedMeta MetaVar Phase [BD]
  | Lift Mode Ty
  | Quote Mode Tm
  | Splice Mode Tm
  | PolU
  | Pol Polarity
  | RepU Pol
  | Rep (RepF Pol Rep)
  deriving (Show)

quoteS :: Mode -> Tm -> Tm
quoteS _ (Splice _ t) = t
quoteS q t = Quote q t

spliceS :: Mode -> Tm -> Tm
spliceS _ (Quote _ t) = t
spliceS q t = Splice q t
