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
    vRepOf,
    vPolOf,
    spineTy,
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
  VLamObj _ _ _ _ b -> b $$ u
  VFlex m mrk sp -> VFlex m mrk (sp :> EAppObj u q i)
  VRigidObj x md a sp -> VRigidObj x md a (sp :> EAppObj u q i)
  VRigidMeta x a sp -> VRigidMeta x a (sp :> EAppObj u q i)
  _ -> error "impossible"

vAppMeta :: Val -> Val -> Icit -> Val
vAppMeta t ~u i = case t of
  VLamMeta _ _ _ b -> b $$ u
  VFlex m mrk sp -> VFlex m mrk (sp :> EAppMeta u i)
  VRigidMeta x a sp -> VRigidMeta x a (sp :> EAppMeta u i)
  _ -> error "impossible"

vSplice :: Mode -> Val -> Val
vSplice q t = case t of
  VQuote _ t -> t
  VFlex m mrk sp -> VFlex m mrk (sp :> ESplice q)
  VRigidMeta x a sp -> VRigidMeta x a (sp :> ESplice q)
  _ -> error "impossible"

vQuote :: Mode -> Val -> Val
vQuote q t = case t of
  VFlex m mrk (sp :> ESplice _) -> VFlex m mrk sp
  VRigidMeta x a (sp :> ESplice _) -> VRigidMeta x a sp
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
  Solved _ v _ -> v
  Unsolved _ _ -> VMeta m mrk

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
  LamObj x q i a t -> VLamObj x q i (eval env a) (Closure env t)
  LamMeta x i a t -> VLamMeta x i (eval env a) (Closure env t)
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
    Solved _ v _ -> force (vAppSp v sp)
    Unsolved _ _ -> t
  t -> t

-- | Apply a pi type to a spine
spineTy :: VTy -> Spine -> VTy
spineTy a = \case
  [] -> a
  sp :> e -> case (force (spineTy a sp), e) of
    (VPiMeta _ _ _ b, EAppMeta u _) -> b $$ u
    (VPiObj _ _ _ _ _ b, EAppObj u _ _) -> b $$ u
    (VLift _ a, ESplice _) -> a
    _ -> error "impossible"

-- | The representation of an object type
vRepOf :: VTy -> VRep
vRepOf a = case force a of
  VUObj {} -> vUnitRep
  VPiObj _ _ _ r _ _ -> force r
  VProducer a -> VRep (RProducer (vRepOf a))
  VFlex m _ sp -> universeRep (spineTy (metaType (lookupMeta m)) sp)
  VRigidObj _ _ ty sp -> universeRep (spineTy ty sp)
  VRigidMeta _ ty sp -> universeRep (spineTy ty sp)
  _ -> error "impossible"
  where
    universeRep t = case force t of
      VUObj _ r -> force r
      _ -> error "impossible"

-- | The polarity of a representation
vPolOf :: VRep -> VPol
vPolOf r = case force r of
  VRep (RUnit th) -> force th
  VRep (RProducer _) -> VPol Neg
  VRep (RArrow _ _) -> VPol Neg
  VFlex m _ sp -> repPol (spineTy (metaType (lookupMeta m)) sp)
  VRigidObj _ _ ty sp -> repPol (spineTy ty sp)
  VRigidMeta _ ty sp -> repPol (spineTy ty sp)
  _ -> error "impossible"
  where
    repPol t = case force t of
      VRepU th -> force th
      _ -> error "impossible"

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  [] -> t
  sp :> EAppObj u q i -> AppObj (quoteSp l t sp) (quote l u) q i
  sp :> EAppMeta u i -> AppMeta (quoteSp l t sp) (quote l u) i
  sp :> ESplice q -> spliceS q (quoteSp l t sp)

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m mrk sp -> quoteSp l (Meta m mrk) sp
  VRigidObj x _ _ sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VRigidMeta x _ sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VLamObj x q i a t -> LamObj x q i (quote l a) (quote (l + 1) (t $$ VVarObj l q a))
  VLamMeta x i a t -> LamMeta x i (quote l a) (quote (l + 1) (t $$ VVarMeta l a))
  VPiObj x q i r a b -> PiObj x q i (quote l r) (quote l a) (quote (l + 1) (b $$ VVarObj l Zero a))
  VPiMeta x i a b -> PiMeta x i (quote l a) (quote (l + 1) (b $$ VVarMeta l a))
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
