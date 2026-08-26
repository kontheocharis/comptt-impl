module Extraction where

import Code (Code (..))
import Common (Ix (..), Lvl (..), Mode (..), lvl2Ix)
import Data.Maybe (fromJust)
import Staging (OTm (..))

-- The environment used during extraction
--
-- It consists of a list of runtime levels
-- that track how many irrelevant variables have been skipped.
data ExEnv = ExEnv {nEnv :: Int, nRuntime :: Int, runtime :: [Maybe Lvl]}

extract :: OTm -> Code
extract = go (ExEnv 0 0 [])
  where
    extend :: ExEnv -> Mode -> ExEnv
    extend (ExEnv n rn real) Zero = ExEnv (n + 1) rn (Nothing : real)
    extend (ExEnv n rn real) Omega = ExEnv (n + 1) (rn + 1) (Just (Lvl rn) : real)

    go :: ExEnv -> OTm -> Code
    go env t = case t of
      OVar x _ -> CVar (lvl2Ix (Lvl (nRuntime env)) (fromJust $ (runtime env) !! unIx (lvl2Ix (Lvl (nEnv env)) x)))
      OApp t u Omega i -> CApp (go env t) (go env u)
      OApp t u Zero i -> go env t
      OLam x Omega i t -> CLam x (go (extend env Omega) t)
      OLam x Zero i t -> go (extend env Zero) t
      OLet x Omega _ t u -> CLet x (go env t) (go (extend env Omega) u)
      OLet x Zero _ t u -> go (extend env Zero) u
      OPi {} -> error "extracting Pi"
      OU -> error "extracting U"
