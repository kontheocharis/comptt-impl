module Evaluation
  ( ($$),
    quote,
    eval,
    nf,
    tryForce,
    quoteU,
    quoteD,
    offsetD,
    offsetU,
    force,
    up,
    down,
    ix2Lvl,
    lvl2Ix,
    vApp,
  )
where

import Common
import Data.Maybe (fromMaybe)
import Metacontext
import Syntax
import Value

infixl 8 $$

($$) :: Closure -> Val -> Val
($$) (Closure env t isd) ~u = eval (env :> ifIsDowned up isd u) t

vApp :: Val -> Val -> Mode -> Icit -> Val
vApp t ~u q i = case t of
  VLam' isd _ _ _ t -> ifIsDowned down isd (t $$ offsetD isd u)
  VFlex isd m mrk sp -> VFlex isd m mrk (sp :> (offsetD isd u, q, i))
  VRigid isd isu x sp -> VRigid isd isu x (sp :> (offsetD isd u, q, i))
  _ -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  [] -> t
  sp :> (u, q, i) -> vApp (vAppSp t sp) u q i

vMeta :: MetaVar -> Marker -> Val
vMeta m mrk = case lookupMeta m of
  Solved _ v -> v
  Unsolved _ -> VMeta m mrk

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([], []) -> v
  (env :> t, bds :> Bound q) -> vApp (vAppBDs env v bds) t q Expl
  (env :> t, bds :> Defined) -> vAppBDs env v bds
  _ -> error "impossible"

eval :: Env -> Tm -> Val
eval env t = case t of
  Var x -> env !! unIx x
  App t u q i -> vApp (eval env t) (eval env u) q i
  Lam x q i t -> VLam x q i (Closure env t NotDowned)
  Pi x q i a b -> VPi x q i (eval env a) (Closure env b NotDowned)
  Let _ _ _ t u -> eval (env :> eval env t) u
  U -> VU
  Meta m mrk -> vMeta m mrk
  InsertedMeta m mrk bds -> vAppBDs env (vMeta m mrk) bds
  Up t -> up (eval env t)
  Down t -> down (eval env t)

moveVal :: Dir -> Val -> Val
moveVal dir v = case v of
  VFlex isd m mrk sp -> VFlex (moveIsDowned dir isd) m mrk sp
  VRigid isd isu x sp -> VRigid (moveIsDowned dir isd) isu x sp
  VLam' isd x q i t -> VLam' (moveIsDowned dir isd) x q i t
  VPi' isu x q i a b -> VPi' (moveIsUpped dir isu) x q i a b
  VU' isu -> VU' (moveIsUpped dir isu)

up :: Val -> Val
up = moveVal Upward

down :: Val -> Val
down = moveVal Downward

tryForce :: Val -> Maybe Val
tryForce v = case v of
  VFlex isd m mrk sp -> case lookupMeta m of
    Solved _ t -> ifIsDowned down isd <$> tryForce (vAppSp t sp)
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
  sp :> (u, q, i) -> App (quoteSp l t sp) (quote l u) q i

quoteD :: IsDowned -> Tm -> Tm
quoteD isd = ifIsDowned downS isd

quoteU :: IsUpped -> Tm -> Tm
quoteU isu = ifIsUpped upS isu

offsetD :: IsDowned -> Val -> Val
offsetD isd = ifIsDowned up isd

offsetU :: IsUpped -> Val -> Val
offsetU isu = ifIsUpped down isu

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex isd m mrk sp -> quoteD isd $ quoteSp l (Meta m mrk) sp
  VRigid isd isu x sp -> quoteD isd $ quoteSp l (quoteU isu (Var (lvl2Ix l x))) sp
  VLam' isd x q i t -> quoteD isd $ Lam x q i (quote (l + 1) (t $$ VVar l q))
  VPi' isu x q i a b -> quoteU isu $ Pi x q i (quote l a) (quote (l + 1) (b $$ VVar l Zero))
  VU' isu -> quoteU isu U

nf :: Marker -> Env -> Tm -> Tm
nf mrk env t = quote (Lvl (length env)) (eval env t)