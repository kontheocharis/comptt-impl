module Evaluation
  ( ($$),
    quote,
    eval,
    nf,
    tryForce,
    force,
    ix2Lvl,
    lvl2Ix,
    vApp,
    vQuote,
    vSplice,
  )
where

import Common
import Data.Maybe (fromMaybe)
import Metacontext
import Syntax
import Value

infixl 8 $$

($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

vApp :: Val -> Val -> Stage -> Mode -> Icit -> Val
vApp t ~u s q i = case t of
  VLam _ _ _ _ t -> t $$ u
  VFlex m mrk sp -> VFlex m mrk (sp :> EApp u s q i)
  VRigid x md sp -> VRigid x md (sp :> EApp u s q i)
  _ -> error "impossible"

vSplice :: Val -> Val
vSplice t = case t of
  VQuote t -> t
  VFlex m mrk sp -> VFlex m mrk (sp :> ESplice)
  VRigid x md sp -> VRigid x md (sp :> ESplice)
  _ -> error "impossible"

vQuote :: Val -> Val
vQuote t = case t of
  VFlex m mrk (sp :> ESplice) -> VFlex m mrk sp
  VRigid x md (sp :> ESplice) -> VRigid x md sp
  t -> VQuote t

vElim :: Val -> Elim -> Val
vElim t = \case
  EApp u s q i -> vApp t u s q i
  ESplice -> vSplice t

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  [] -> t
  sp :> e -> vElim (vAppSp t sp) e

vMeta :: MetaVar -> Marker -> Val
vMeta m mrk = case lookupMeta m of
  Solved _ v -> v
  Unsolved _ -> VMeta m mrk

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([], []) -> v
  (env :> t, bds :> Bound s q) -> vApp (vAppBDs env v bds) t s q Expl
  (env :> t, bds :> Defined) -> vAppBDs env v bds
  _ -> error "impossible"

eval :: Env -> Tm -> Val
eval env t = case t of
  Var x _ -> env !! unIx x
  App t u s q i -> vApp (eval env t) (eval env u) s q i
  Lam x s q i t -> VLam x s q i (Closure env t)
  Pi x s q i a b -> VPi x s q i (eval env a) (Closure env b)
  Let _ _ _ _ t u -> eval (env :> eval env t) u
  U s -> VU s
  Meta m mrk -> vMeta m mrk
  InsertedMeta m mrk bds -> vAppBDs env (vMeta m mrk) bds
  Lift a -> VLift (eval env a)
  Quote t -> vQuote (eval env t)
  Splice t -> vSplice (eval env t)

tryForce :: Val -> Maybe Val
tryForce v = case v of
  VFlex m mrk sp -> case lookupMeta m of
    Solved _ t -> tryForce (vAppSp t sp)
    Unsolved _ -> Nothing
  t -> Just t

force :: Val -> Val
force t = fromMaybe t (tryForce t)

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

ix2Lvl :: Lvl -> Ix -> Lvl
ix2Lvl (Lvl l) (Ix x) = Lvl (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  [] -> t
  sp :> EApp u s q i -> App (quoteSp l t sp) (quote l u) s q i
  sp :> ESplice -> spliceS (quoteSp l t sp)

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m mrk sp -> quoteSp l (Meta m mrk) sp
  VRigid x md sp -> quoteSp l (Var (lvl2Ix l x) md) sp
  VLam x s q i t -> Lam x s q i (quote (l + 1) (t $$ VVar l q))
  VPi x s q i a b -> Pi x s q i (quote l a) (quote (l + 1) (b $$ VVar l Zero))
  VU s -> U s
  VLift a -> Lift (quote l a)
  VQuote t -> quoteS (quote l t)

nf :: Marker -> Env -> Tm -> Tm
nf mrk env t = quote (Lvl (length env)) (eval env t)
