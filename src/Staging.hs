module Staging (stage, OTm (..), quoteO) where

import Common
import Control.Exception (throwIO)
import Control.Monad (when)
import Errors
import Evaluation (quote)
import Metacontext
import Syntax

newtype ORep = ORep (RepF Polarity ORep)

-- Object code, with de Bruijn levels for variables
data OTm
  = OVar Lvl Mode
  | OLam Name Mode Icit OTm
  | OApp OTm OTm Mode Icit
  | OPi Name Mode Icit ORep OTm OTm
  | OProducer OTm
  | ORet OTm
  | OLet Name Mode OTm OTm OTm
  | OU Polarity ORep

data SVal
  = SCode OTm
  | SClos SEnv Tm
  | SPol Polarity
  | SRep ORep
  | SDummy

type SEnv = [SVal]

stageObj :: SVal -> OTm
stageObj (SCode t) = t
stageObj _ = error "staging meta-level thing"

stagePol :: SVal -> Polarity
stagePol (SPol th) = th
stagePol _ = error "staging non-polarity"

stageRep :: SVal -> ORep
stageRep (SRep r) = r
stageRep _ = error "staging non-representation"

sAppObj :: SVal -> SVal -> Mode -> Icit -> SVal
sAppObj t u q i = SCode (OApp (stageObj t) (stageObj u) q i)

sAppMeta :: Lvl -> SVal -> SVal -> SVal
sAppMeta l t u = case t of
  SClos env b -> go l (env :> u) b
  _ -> error "impossible"

appBDs :: Lvl -> SEnv -> SVal -> [BD] -> SVal
appBDs l env ~v bds = case (env, bds) of
  ([], []) -> v
  (env :> t, bds :> Bound _ _) -> sAppMeta l (appBDs l env v bds) t
  (env :> _, bds :> Defined) -> appBDs l env v bds
  _ -> error "impossible"

metaSVal :: Lvl -> MetaVar -> SVal
metaSVal l m = case lookupMeta m of
  Solved _ v -> go l [] (quote 0 v)
  Unsolved _ -> error "impossible"

go :: Lvl -> SEnv -> Tm -> SVal
go l env = \case
  Var x -> env !! unIx x
  LamMeta _ _ t -> SClos env t
  LamObj x q i t ->
    SCode (OLam x q i (stageObj (go (l + 1) (env :> SCode (OVar l q)) t)))
  AppObj t u q i -> sAppObj (go l env t) (go l env u) q i
  AppMeta t u _ -> sAppMeta l (go l env t) (go l env u)
  Let _ SMeta _ _ t u -> go l (env :> go l env t) u
  Let x SObj q a t u ->
    SCode . OLet x q (stageObj (go l env a)) (stageObj (go l env t)) $
      stageObj (go (l + 1) (env :> SCode (OVar l q)) u)
  PiObj x q i r a b ->
    SCode . OPi x q i (stageRep (go l env r)) (stageObj (go l env a)) $
      stageObj (go (l + 1) (env :> SCode (OVar l Zero)) b)
  Producer a -> SCode (OProducer (stageObj (go l env a)))
  Ret t -> SCode (ORet (stageObj (go l env t)))
  UObj th a -> SCode (OU (stagePol (go l env th)) (stageRep (go l env a)))
  Meta m _ -> metaSVal l m
  InsertedMeta m _ bds -> appBDs l env (metaSVal l m) bds
  Quote _ t -> go l env t
  Splice _ t -> go l env t
  PiMeta {} -> SDummy
  UMeta -> SDummy
  Lift {} -> SDummy
  PolU -> SDummy
  Pol th -> SPol th
  RepU {} -> SDummy
  Rep r -> SRep (ORep (bimapRepF (stagePol . go l env) (stageRep . go l env) r))

quoteORep :: ORep -> Rep
quoteORep (ORep r) = Rep (bimapRepF Pol quoteORep r)

quoteO :: Lvl -> OTm -> Tm
quoteO l = \case
  OVar x _ -> Var (lvl2Ix l x)
  OLam x q i t -> LamObj x q i (quoteO (l + 1) t)
  OApp t u q i -> AppObj (quoteO l t) (quoteO l u) q i
  OPi x q i r a b -> PiObj x q i (quoteORep r) (quoteO l a) (quoteO (l + 1) b)
  OProducer a -> Producer (quoteO l a)
  ORet t -> Ret (quoteO l t)
  OLet x q a t u -> Let x SObj q (quoteO l a) (quoteO l t) (quoteO (l + 1) u)
  OU th a -> UObj (Pol th) (quoteORep a)

stage :: SourcePos -> Tm -> IO OTm
stage pos t = do
  anyUnsolved >>= \u -> when u (throwIO $ Error pos (ExtractError CannotExtractMeta))
  pure $ stageObj (go 0 [] t)
