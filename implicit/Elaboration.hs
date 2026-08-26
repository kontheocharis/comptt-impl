module Elaboration (check, infer, inferIn) where

import Common
import Control.Exception
import Control.Monad
import Cxt
import Data.Function ((&))
import Data.IORef
import qualified Data.IntMap as IM
import Errors
import Evaluation
import Metacontext
import qualified Presyntax as P
import Syntax
import Unification
import Value

-- Elaboration
--------------------------------------------------------------------------------

freshMeta :: Cxt -> Mode -> IO Tm
freshMeta cxt q = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  -- Always make a meta in mode ω, but add # to its context if
  -- possible.
  -- Specifically, # is added if we are asking for a meta in mode 0, or the
  -- context is already has #.
  let mrk =
        marker cxt & case q of
          Zero -> ext Present
          Omega -> id
  modifyIORef' mcxt $ IM.insert m (Unsolved mrk)
  pure $ (InsertedMeta (MetaVar m) mrk (bds cxt))

elabError :: Cxt -> ElabError -> IO a
elabError cxt e = throwIO $ Error (pos cxt) (ElabError cxt e)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  unify (lvl cxt) t t'
    `catch` \e -> elabError cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t') e

insert' :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act
  where
    go (t, va) = case force va of
      VPi x q Impl a b -> do
        m <- freshMeta cxt q
        let mv = eval (env cxt) m
        go (App t m q Impl, b $$ mv)
      va -> pure (t, va)

insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act =
  act >>= \case
    (t@(Lam _ q Impl _), va) -> pure (t, va)
    (t, va) -> insert' cxt (pure (t, va))

insertUntilName :: Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act
  where
    go (t, va) = case force va of
      va@(VPi x q Impl a b) -> do
        if x == name
          then
            pure (t, va)
          else do
            m <- freshMeta cxt q
            let mv = eval (env cxt) m
            go (App t m q Impl, b $$ mv)
      _ -> elabError cxt $ NoNamedImplicitArg name

-- Check in a given mode
--
-- check : (Γ : Ctx) -> (i : {0, ω}) -> PTm -> Ty Γ -> TC (Tm i A)
--
-- By the identification Ty Γ = Tm 0 Γ U, types are always in mode 0.
checkIn :: Cxt -> Mode -> P.Tm -> VTy -> IO Tm
checkIn cxt Zero t a = check (enterMarker cxt) t a
checkIn cxt Omega t a = check cxt t a

-- Check in mode ω (default)
check :: Cxt -> P.Tm -> VTy -> IO Tm
check cxt t a = case (t, force a) of
  (P.SrcPos pos t, a) ->
    check (cxt {pos = pos}) t a
  (P.Lam x i t, VPi x' q' i' a b) | either (\x -> x == x' && i' == Impl) (== i') i -> do
    -- Here we must wrap the variable in ↓ if the q = ω, because of the lambda rule.
    Lam x q' i' <$> check (bind cxt x q' a) t (b $$ VVar (lvl cxt) q')
  (t, VPi x q Impl a b) -> do
    Lam x q Impl <$> check (newBinder cxt x q a) t (b $$ VVar (lvl cxt) q)
  (P.Let x q a t u, a') -> do
    -- Types always in mode 0
    a <- checkIn cxt Zero a VU
    let ~va = eval (env cxt) a
    t <- checkIn cxt q t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x q vt va) u a'
    pure (Let x q a t u)
  (P.Hole, a) ->
    freshMeta cxt Omega
  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt t
    unifyCatch cxt expected inferred
    pure t

inferIn :: Cxt -> Mode -> P.Tm -> IO (Tm, VTy)
inferIn cxt Zero t = infer (enterMarker cxt) t
inferIn cxt Omega t = infer cxt t

-- Mode ω
--
-- types always in mode 0
infer :: Cxt -> P.Tm -> IO (Tm, VTy)
infer cxt = \case
  P.SrcPos pos t ->
    infer (cxt {pos = pos}) t
  P.Var x -> do
    let go ix (types :> (x', origin, q, a))
          | x == x' && origin == Source = case (marker cxt, q) of
              -- A variable is usable unless it is mode 0 and the context lacks #
              (Absent, Omega) -> pure (Var ix q, a)
              (Absent, Zero) -> elabError cxt $ InsufficientMode
              (Present, Omega) -> pure (Var ix q, a)
              (Present, Zero) -> pure (Var ix q, a)
          | otherwise = go (ix + 1) types
        go ix [] =
          elabError cxt $ NameNotInScope x
    go 0 (types cxt)
  P.Lam x (Right i) t -> do
    -- By default infer a runtime lambda
    let q = Omega
    a <- eval (env cxt) <$> freshMeta cxt Zero
    let cxt' = bind cxt x q a
    (t, b) <- insert cxt' $ infer cxt' t
    -- When b is instantiated with some term (0 u : A), we might need to wrap it
    -- in ↑; This is because b is in the context extended by (q x : A), but the
    -- Π type codomain is over (0 x : A).
    pure (Lam x q i t, VPi x q i a $ closeVal cxt b)
  P.Lam x Left {} t ->
    elabError cxt $ InferNamedLam
  P.App t u i -> do
    -- choose implicit insertion
    (i, t, tty) <- case i of
      Left name -> do
        (t, tty) <- insertUntilName cxt name $ infer cxt t
        pure (Impl, t, tty)
      Right Impl -> do
        (t, tty) <- infer cxt t
        pure (Impl, t, tty)
      Right Expl -> do
        (t, tty) <- insert' cxt $ infer cxt t
        pure (Expl, t, tty)

    (q, a, b) <- case force tty of
      VPi x q i' a b -> do
        unless (i == i') $ elabError cxt $ IcitMismatch i i'
        pure (q, a, b)
      tty -> do
        let q = Omega
        a <- eval (env cxt) <$> freshMeta cxt Zero
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" q a) Zero
        unifyCatch cxt tty (VPi "x" q i a b)
        pure (q, a, b)

    u <- checkIn cxt q u a
    -- Need to wrap substitution in ↓ if q = ω, because of the application rule.
    pure (App t u q i, b $$ eval (env cxt) u)
  -- Elaborating types will always require #, because they are only valid in mode 0.
  P.U -> do
    when (marker cxt /= Present) (elabError cxt $ InsufficientMode)
    pure (U, VU)
  P.Pi x q i a b -> do
    when (marker cxt /= Present) (elabError cxt $ InsufficientMode)
    a <- checkIn cxt Zero a VU
    b <- checkIn (bind cxt x Zero (eval (env cxt) a)) Zero b VU
    pure (Pi x q i a b, VU)
  P.Let x q a t u -> do
    a <- checkIn cxt Zero a VU
    let ~va = eval (env cxt) a
    t <- checkIn cxt q t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x q vt va) u
    pure (Let x q a t u, b)
  P.Hole -> do
    a <- eval (env cxt) <$> freshMeta cxt Zero
    t <- freshMeta cxt Omega
    pure (t, a)
