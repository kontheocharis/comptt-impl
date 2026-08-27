module Evaluation
  ( ($$),
    quote,
    eval,
    nf,
    force,
    ix2Lvl,
    lvl2Ix,
    vAppObj,
    vAppMeta,
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

vAppObj :: Val -> Val -> Mode -> Icit -> Val
vAppObj t ~u q i = case t of
  VLamObj _ _ _ b -> b $$ u
  VFlex m mrk sp -> VFlex m mrk (sp :> EAppObj u q i)
  VRigidObj x md sp -> VRigidObj x md (sp :> EAppObj u q i)
  VRigidMeta x sp -> VRigidMeta x (sp :> EAppObj u q i)
  _ -> error "impossible"

vAppMeta :: Val -> Val -> Icit -> Val
vAppMeta t ~u i = case t of
  VLamMeta _ _ b -> b $$ u
  VFlex m mrk sp -> VFlex m mrk (sp :> EAppMeta u i)
  VRigidMeta x sp -> VRigidMeta x (sp :> EAppMeta u i)
  _ -> error "impossible"

vSplice :: Mode -> Val -> Val
vSplice q t = case t of
  VQuote _ t -> t
  VFlex m mrk sp -> VFlex m mrk (sp :> ESplice q)
  VRigidMeta x sp -> VRigidMeta x (sp :> ESplice q)
  _ -> error "impossible"

vQuote :: Mode -> Val -> Val
vQuote q t = case t of
  VFlex m mrk (sp :> ESplice _) -> VFlex m mrk sp
  VRigidMeta x (sp :> ESplice _) -> VRigidMeta x sp
  t -> VQuote q t

vElim :: Val -> Elim -> Val
vElim t = \case
  EAppObj u q i -> vAppObj t u q i
  EAppMeta u i -> vAppMeta t u i
  ESplice q -> vSplice q t

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
  (env :> t, bds :> Bound SObj q) -> vAppMeta (vAppBDs env v bds) (vQuote q t) Expl
  (env :> t, bds :> Bound SMeta _) -> vAppMeta (vAppBDs env v bds) t Expl
  (env :> t, bds :> Defined) -> vAppBDs env v bds
  _ -> error "impossible"

eval :: Env -> Tm -> Val
eval env t = case t of
  Var x -> env !! unIx x
  AppObj t u q i -> vAppObj (eval env t) (eval env u) q i
  AppMeta t u i -> vAppMeta (eval env t) (eval env u) i
  LamObj x q i t -> VLamObj x q i (Closure env t)
  LamMeta x i t -> VLamMeta x i (Closure env t)
  PiObj x q i r a b -> VPiObj x q i (eval env r) (eval env a) (Closure env b)
  PiMeta x i a b -> VPiMeta x i (eval env a) (Closure env b)
  Producer a -> VProducer (eval env a)
  Ret t -> VRet (eval env t)
  Let _ _ _ _ t u -> eval (env :> eval env t) u
  UMeta -> VUMeta
  UObj th a -> VUObj (eval env th) (eval env a)
  Meta m mrk -> vMeta m mrk
  InsertedMeta m mrk bds -> vAppBDs env (vMeta m mrk) bds
  Lift q a -> VLift q (eval env a)
  Quote q t -> vQuote q (eval env t)
  Splice q t -> vSplice q (eval env t)
  PolU -> VPolU
  Pol p -> VPol p
  RepU th -> VRepU (eval env th)
  Rep r -> VRep (bimapRepF (eval env) (eval env) r)

force :: Val -> Val
force t = case t of
  VFlex m _ sp -> case lookupMeta m of
    Solved _ v -> force (vAppSp v sp)
    Unsolved _ -> t
  t -> t

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  [] -> t
  sp :> EAppObj u q i -> AppObj (quoteSp l t sp) (quote l u) q i
  sp :> EAppMeta u i -> AppMeta (quoteSp l t sp) (quote l u) i
  sp :> ESplice q -> spliceS q (quoteSp l t sp)

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m mrk sp -> quoteSp l (Meta m mrk) sp
  VRigidObj x _ sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VRigidMeta x sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VLamObj x q i t -> LamObj x q i (quote (l + 1) (t $$ VVarObj l q))
  VLamMeta x i t -> LamMeta x i (quote (l + 1) (t $$ VVarMeta l))
  VPiObj x q i r a b -> PiObj x q i (quote l r) (quote l a) (quote (l + 1) (b $$ VVarObj l Zero))
  VPiMeta x i a b -> PiMeta x i (quote l a) (quote (l + 1) (b $$ VVarMeta l))
  VProducer a -> Producer (quote l a)
  VRet t -> Ret (quote l t)
  VUMeta -> UMeta
  VUObj th a -> UObj (quote l th) (quote l a)
  VLift q a -> Lift q (quote l a)
  VQuote q t -> quoteS q (quote l t)
  VPolU -> PolU
  VPol p -> Pol p
  VRepU th -> RepU (quote l th)
  VRep r -> Rep (bimapRepF (quote l) (quote l) r)

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)
