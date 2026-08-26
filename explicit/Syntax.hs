module Syntax where

import Common

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name Mode Icit Tm
  | App Tm Tm Mode Icit
  | U
  | Pi Name Mode Icit Ty Ty
  | Let Name Mode Ty Tm Tm
  | Meta MetaVar Marker
  | InsertedMeta MetaVar Marker [BD]
  | Up Tm
  | Down Tm
  deriving (Show)

-- Shallowly eliminate Up and Down constructors:

downS :: Tm -> Tm
downS (Up t) = t
downS t = Down t

upS :: Tm -> Tm
upS (Down t) = t
upS t = Up t
