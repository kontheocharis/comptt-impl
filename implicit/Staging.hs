module Staging (stage, OTm (..), quoteO) where

import Common
import Control.Exception (throwIO)
import Control.Monad (when)
import Errors
import Evaluation (quote)
import Metacontext
import Syntax

-- Object code, with de Bruijn levels for variables
data OTm
  = OVar Lvl Mode
  | OLam Name Mode Icit OTm
  | OApp OTm OTm Mode Icit
  | OPi Name Mode Icit OTm OTm
  | OLet Name Mode OTm OTm OTm
  | OU

data SVal
  = SCode OTm
  | SClos SEnv Tm
  | SDummy

type SEnv = [SVal]

stageObj :: SVal -> OTm
stageObj (SCode t) = t
stageObj _ = error "staging meta-level thing"

sApp :: Lvl -> SVal -> SVal -> Stage -> Mode -> Icit -> SVal
sApp l t u s q i = case (s, t) of
  (SMeta, SClos env b) -> go l (env :> u) b
  (SMeta, _) -> error "impossible"
  (SObj, _) -> SCode (OApp (stageObj t) (stageObj u) q i)

appBDs :: Lvl -> SEnv -> SVal -> [BD] -> SVal
appBDs l env ~v bds = case (env, bds) of
  ([], []) -> v
  (env :> t, bds :> Bound s q) -> sApp l (appBDs l env v bds) t s q Expl
  (env :> _, bds :> Defined) -> appBDs l env v bds
  _ -> error "impossible"

metaSVal :: Lvl -> MetaVar -> SVal
metaSVal l m = case lookupMeta m of
  Solved _ v -> go l [] (quote 0 v)
  Unsolved _ -> error "impossible"

go :: Lvl -> SEnv -> Tm -> SVal
go l env = \case
  Var x _ -> env !! unIx x
  Lam _ SMeta _ _ t -> SClos env t
  Lam x SObj q i t ->
    SCode (OLam x q i (stageObj (go (l + 1) (env :> SCode (OVar l q)) t)))
  App t u s q i -> sApp l (go l env t) (go l env u) s q i
  Let _ SMeta _ _ t u -> go l (env :> go l env t) u
  Let x SObj q a t u ->
    SCode . OLet x q (stageObj (go l env a)) (stageObj (go l env t)) $
      stageObj (go (l + 1) (env :> SCode (OVar l q)) u)
  Pi x SObj q i a b ->
    SCode . OPi x q i (stageObj (go l env a)) $
      stageObj (go (l + 1) (env :> SCode (OVar l (stageMode SObj))) b)
  U SObj -> SCode OU
  Meta m _ -> metaSVal l m
  InsertedMeta m _ bds -> appBDs l env (metaSVal l m) bds
  Quote _ t -> go l env t
  Splice _ t -> go l env t
  Pi _ SMeta _ _ _ _ -> SDummy
  U SMeta -> SDummy
  Lift {} -> SDummy
  PolU -> SDummy
  Pol _ -> SDummy
  RepU {} -> SDummy
  Rep {} -> SDummy

quoteO :: Lvl -> OTm -> Tm
quoteO l = \case
  OVar x q -> Var (lvl2Ix l x) q
  OLam x q i t -> Lam x SObj q i (quoteO (l + 1) t)
  OApp t u q i -> App (quoteO l t) (quoteO l u) SObj q i
  OPi x q i a b -> Pi x SObj q i (quoteO l a) (quoteO (l + 1) b)
  OLet x q a t u -> Let x SObj q (quoteO l a) (quoteO l t) (quoteO (l + 1) u)
  OU -> U SObj

stage :: SourcePos -> Tm -> IO OTm
stage pos t = do
  anyUnsolved >>= \u -> when u (throwIO $ Error pos (ExtractError CannotExtractMeta))
  pure $ stageObj (go 0 [] t)
