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

-- There is a functor from the syntactic category of TTᶜ to the free meet
-- semilattice on {$, #} as a poset. We call this functor Phase.

data Cxt = Cxt
  { -- used for:
    -----------------------------------
    env :: Env, -- evaluation
    lvl :: Lvl, -- unification
    types :: Types, -- raw name lookup, pretty printing
    bds :: [BD], -- fresh meta creation
    pos :: SourcePos, -- error reporting
    phase :: Phase -- the phase of the context -- Phase Γ
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
emptyCxt p = Cxt [] 0 [] [] p topPhase

-- Γ ↦ Γ, i x : A
bind :: Cxt -> Name -> Stage -> Mode -> VTy -> Cxt
bind (Cxt env l types bds pos ph) x s q ~a =
  Cxt (env :> vVar l s q a) (l + 1) (types :> (x, Source, s, q, a)) (bds :> Bound s q) pos ph

-- Γ ↦ Γ, i x : A
newBinder :: Cxt -> Name -> Stage -> Mode -> VTy -> Cxt
newBinder (Cxt env l types bds pos ph) x s q ~a =
  Cxt (env :> vVar l s q a) (l + 1) (types :> (x, Inserted, s, q, a)) (bds :> Bound s q) pos ph

-- Γ ↦ Γ, i x := t
define :: Cxt -> Name -> Stage -> Mode -> Val -> VTy -> Cxt
define (Cxt env l types bds pos ph) x s q ~t ~a =
  Cxt (env :> t) (l + 1) (types :> (x, Source, s, q, a)) (bds :> Defined) pos ph

-- | closeVal : (Γ : Con) → Val (Γ, i x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)

-- | closeTy : (Γ : Con) → ValTy Γ → Ty ∙
-- Does by wrapping in Πs
-- @@Todo: improve this like in elab-zoo/05-pruning
closeTy :: Cxt -> VTy -> Ty
closeTy cxt a = go 0 [] (reverse (zip3 (env cxt) (types cxt) (bds cxt)))
  where
    subst l sub v = eval sub (quote l v)
    go l sub [] = quote l (subst l sub a)
    go l sub ((t, (x, _, _, _, ty), bd) : rest) = case bd of
      Bound SObj q ->
        let vty = subst l sub ty
         in PiMeta x Expl (Lift q (quote l vty)) $
              go (l + 1) (sub :> vSplice q (VVarMeta l (VLift q vty))) rest
      Bound SMeta _ ->
        let vty = subst l sub ty
         in PiMeta x Expl (quote l vty) $
              go (l + 1) (sub :> VVarMeta l vty) rest
      Defined ->
        go (l + 1) (sub :> subst l sub t) rest

-- | Γ ↦ Γ, P
enterPhase :: Phase -> Cxt -> Cxt
enterPhase p (Cxt env l types bds pos ph) = Cxt env l types bds pos (meetPhase ph p)
