module Extraction where

import Code (Code (..))
import Common (Ix (..), Lvl (..), Mode (..), SourcePos)
import Control.Exception (throwIO)
import Control.Monad (when)
import Data.Maybe (fromJust)
import Errors
import Evaluation
import Metacontext (anyUnsolved)
import Syntax (Tm (..))
import Value (Env, pattern VVar)

-- The environment used during extraction
--
-- It consists of the evaluation environment, and a list of runtime levels
-- that track how many irrelevant variables have been skipped.
data ExEnv = ExEnv {nEnv :: Int, env :: Env, nRuntime :: Int, runtime :: [Maybe Lvl]}

-- Only allowed to extract closed terms
extract :: SourcePos -> Tm -> IO Code
extract pos t = do
  anyUnsolved >>= \u -> when u (throwIO $ Error (pos) (ExtractError CannotExtractMeta))
  pure $ go (ExEnv 0 [] 0 []) t
  where
    extend :: ExEnv -> Mode -> ExEnv
    extend (ExEnv n env rn real) q@Zero = ExEnv (n + 1) (VVar (Lvl n) q : env) rn (Nothing : real)
    extend (ExEnv n env rn real) q@Omega = ExEnv (n + 1) (VVar (Lvl n) q : env) (rn + 1) (Just (Lvl rn) : real)

    goMeta :: ExEnv -> Tm -> Code
    goMeta exenv t = case tryForce (eval (env exenv) t) of
      Just t' -> go exenv (quote (Lvl (nEnv exenv)) t')
      Nothing -> error "impossible"

    go :: ExEnv -> Tm -> Code
    go env t = case t of
      Var (Ix x) _ -> CVar (lvl2Ix (Lvl (nRuntime env)) (fromJust $ (runtime env) !! x))
      App t u Omega i -> CApp (go env t) (go env u)
      App t u Zero i -> go env t
      Lam x Omega i t -> CLam x (go (extend env Omega) t)
      Lam x Zero i t -> go (extend env Zero) t
      Let x Omega _ t u -> CLet x (go env t) (go (extend env Omega) u)
      Let x Zero _ t u -> go (extend env Zero) u
      Meta _ _ -> goMeta env t
      InsertedMeta _ _ _ -> goMeta env t
      Pi x q i a b -> error "extracting Pi"
      U -> error "extracting U"