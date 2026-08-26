module Cxt where

import Common
import Evaluation
import Pretty
import Syntax
import Value

-- Elaboration context
--------------------------------------------------------------------------------

data NameOrigin = Inserted | Source deriving (Eq)

type Types = [(String, NameOrigin, Stage, Mode, VTy)]

data Cxt = Cxt
  { -- used for:
    -----------------------------------
    env :: Env, -- evaluation
    lvl :: Lvl, -- unification
    types :: Types, -- raw name lookup, pretty printing
    bds :: [BD], -- fresh meta creation
    pos :: SourcePos, -- error reporting
    marker :: Marker -- whether # is present or absent
  }

cxtNames :: Cxt -> [Name]
cxtNames = fmap (\(x, _, _, _, _) -> x) . types

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quote (lvl cxt) v) []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt p = Cxt [] 0 [] [] p Absent

-- Γ ↦ Γ, i x : A
bind :: Cxt -> Name -> Stage -> Mode -> VTy -> Cxt
bind (Cxt env l types bds pos md) x s q ~a =
  Cxt (env :> VVar l q) (l + 1) (types :> (x, Source, s, q, a)) (bds :> Bound s q) pos md

-- Γ ↦ Γ, i x : A
newBinder :: Cxt -> Name -> Stage -> Mode -> VTy -> Cxt
newBinder (Cxt env l types bds pos md) x s q ~a =
  Cxt (env :> VVar l q) (l + 1) (types :> (x, Inserted, s, q, a)) (bds :> Bound s q) pos md

-- Γ ↦ Γ, i x := t
define :: Cxt -> Name -> Stage -> Mode -> Val -> VTy -> Cxt
define (Cxt env l types bds pos md) x s q ~t ~a =
  Cxt (env :> t) (l + 1) (types :> (x, Source, s, q, a)) (bds :> Defined) pos md

-- | closeVal : (Γ : Con) → Val (Γ, i x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)

-- | Γ ↦ Γ, #
enterMarker :: Cxt -> Cxt
enterMarker (Cxt env l types bds pos _) = Cxt env l types bds pos Present
