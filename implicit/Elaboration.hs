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

freshMeta :: Cxt -> Stage -> Mode -> IO Tm
freshMeta cxt s q = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  let mrk = marker (withMarker s q cxt)
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
      VPi x s q Impl a b -> do
        m <- freshMeta cxt s q
        let mv = eval (env cxt) m
        go (App t m s q Impl, b $$ mv)
      va -> pure (t, va)

insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act =
  act >>= \case
    (t@(Lam _ _ q Impl _), va) -> pure (t, va)
    (t, va) -> insert' cxt (pure (t, va))

insertUntilName :: Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act
  where
    go (t, va) = case force va of
      va@(VPi x s q Impl a b) -> do
        if x == name
          then
            pure (t, va)
          else do
            m <- freshMeta cxt s q
            let mv = eval (env cxt) m
            go (App t m s q Impl, b $$ mv)
      _ -> elabError cxt $ NoNamedImplicitArg name

-- Check in a given mode
--
-- check : (Γ : Ctx) -> (i : {0, ω}) -> PTm -> Ty Γ -> TC (Tm i A)
--
-- By the identification Ty Γ = Tm 0 Γ U, types are always in mode 0.
withMarker :: Stage -> Mode -> Cxt -> Cxt
withMarker SObj Zero = enterMarker
withMarker _ _ = id

checkIn :: Cxt -> Stage -> Mode -> P.Tm -> VTy -> IO Tm
checkIn cxt s q t a = check (withMarker s q cxt) s t a

-- Check whether the given mode on a binder is valid in the given stage. We
-- default to `runtime` mode for meta-binders, which is easier than some kind of
-- mutually-exclusive pair of optional values.
checkBinderMode :: Cxt -> Stage -> Mode -> IO ()
checkBinderMode cxt SMeta Zero = elabError cxt ErasedMetaBinder
checkBinderMode _ _ _ = pure ()

checkMetaOnly :: Cxt -> Stage -> IO ()
checkMetaOnly cxt s = when (s /= SMeta) (elabError cxt $ StageMismatch s SMeta)

checkRep :: Cxt -> Polarity -> P.Tm -> IO Tm
checkRep cxt th a = check cxt SMeta a (VRepU (VPol th))

-- Check in mode ω (default)
check :: Cxt -> Stage -> P.Tm -> VTy -> IO Tm
check cxt s t a = case (t, force a) of
  (P.SrcPos pos t, a) ->
    check (cxt {pos = pos}) s t a
  (P.Lam x i t, VPi x' s' q' i' a b) | either (\x -> x == x' && i' == Impl) (== i') i -> do
    -- Here we must wrap the variable in ↓ if the q = ω, because of the lambda rule.
    Lam x s' q' i' <$> check (bind cxt x s' q' a) s' t (b $$ VVar (lvl cxt) q')
  (t, VPi x s' q Impl a b) -> do
    Lam x s' q Impl <$> check (newBinder cxt x s' q a) s' t (b $$ VVar (lvl cxt) q)
  (P.Let x s' q a t u, a') -> do
    checkBinderMode cxt s' q
    a <- checkIn cxt s' (stageMode s') a (VU s')
    let ~va = eval (env cxt) a
    t <- checkIn cxt s' q t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x s' q vt va) s u a'
    pure (Let x s' q a t u)
  (P.Quote t, VLift q a) -> do
    when (s /= SMeta) (elabError cxt $ StageMismatch s SMeta)
    quoteS q <$> checkIn cxt SObj q t a
  (P.Hole, a) ->
    freshMeta cxt s Omega
  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt s t
    unifyCatch cxt expected inferred
    pure t

inferIn :: Cxt -> Stage -> Mode -> P.Tm -> IO (Tm, VTy)
inferIn cxt s q t = infer (withMarker s q cxt) s t

-- Mode ω
infer :: Cxt -> Stage -> P.Tm -> IO (Tm, VTy)
infer cxt s = \case
  P.SrcPos pos t ->
    infer (cxt {pos = pos}) s t
  P.Var x -> do
    let go ix (types :> (x', origin, s', q, a))
          | x == x' && origin == Source = do
              when (s /= s') (elabError cxt $ StageMismatch s s')
              case (marker cxt, q) of
                -- A variable is usable unless it is mode 0 and the context lacks #
                (Absent, Zero) -> elabError cxt $ InsufficientMode
                _ -> pure (Var ix q, a)
          | otherwise = go (ix + 1) types
        go ix [] =
          elabError cxt $ NameNotInScope x
    go 0 (types cxt)
  P.Lam x (Right i) t -> do
    -- By default infer a runtime lambda
    let q = Omega
    a <- eval (env cxt) <$> freshMeta cxt s (stageMode s)
    let cxt' = bind cxt x s q a
    (t, b) <- insert cxt' $ infer cxt' s t
    -- When b is instantiated with some term (0 u : A), we might need to wrap it
    -- in ↑; This is because b is in the context extended by (q x : A), but the
    -- Π type codomain is over (0 x : A).
    pure (Lam x s q i t, VPi x s q i a $ closeVal cxt b)
  P.Lam x Left {} t ->
    elabError cxt $ InferNamedLam
  P.App t u i -> do
    -- choose implicit insertion
    (i, t, tty) <- case i of
      Left name -> do
        (t, tty) <- insertUntilName cxt name $ infer cxt s t
        pure (Impl, t, tty)
      Right Impl -> do
        (t, tty) <- infer cxt s t
        pure (Impl, t, tty)
      Right Expl -> do
        (t, tty) <- insert' cxt $ infer cxt s t
        pure (Expl, t, tty)

    (s', q, a, b) <- case force tty of
      VPi x s' q i' a b -> do
        unless (i == i') $ elabError cxt $ IcitMismatch i i'
        pure (s', q, a, b)
      tty -> do
        let q = Omega
        a <- eval (env cxt) <$> freshMeta cxt s (stageMode s)
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" s q a) s (stageMode s)
        unifyCatch cxt tty (VPi "x" s q i a b)
        pure (s, q, a, b)

    u <- checkIn cxt s' q u a
    -- Need to wrap substitution in ↓ if q = ω, because of the application rule.
    pure (App t u s' q i, b $$ eval (env cxt) u)
  -- Object types are only valid in mode 0, so they require #.
  P.U s' -> do
    when (s' == SObj && marker cxt /= Present) (elabError cxt $ InsufficientMode)
    pure (U s', VU s')
  P.Lift q a -> do
    a <- checkIn cxt SObj Zero a (VU SObj)
    pure (Lift q a, VU SMeta)
  P.PolU -> do
    checkMetaOnly cxt s
    pure (PolU, VU SMeta)
  P.Pol th -> do
    checkMetaOnly cxt s
    pure (Pol th, VPolU)
  P.RepU th -> do
    checkMetaOnly cxt s
    th <- check cxt SMeta th VPolU
    pure (RepU th, VU SMeta)
  P.Rep (RUnit th) -> do
    checkMetaOnly cxt s
    th <- check cxt SMeta th VPolU
    pure (Rep (RUnit th), VRepU (eval (env cxt) th))
  P.Rep (RProducer a) -> do
    checkMetaOnly cxt s
    a <- checkRep cxt Pos a
    pure (Rep (RProducer a), VRepU (VPol Neg))
  P.Rep (RArrow a b) -> do
    checkMetaOnly cxt s
    a <- checkRep cxt Pos a
    b <- checkRep cxt Neg b
    pure (Rep (RArrow a b), VRepU (VPol Neg))
  P.Quote t -> do
    when (s /= SMeta) (elabError cxt $ StageMismatch s SMeta)
    (t, a) <- inferIn cxt SObj Omega t
    pure (quoteS Omega t, VLift Omega a)
  P.Splice t -> do
    when (s /= SObj) (elabError cxt $ StageMismatch s SObj)
    (t, tty) <- infer cxt SMeta t
    case force tty of
      VLift q a -> do
        when (q == Zero && marker cxt /= Present) (elabError cxt $ InsufficientMode)
        pure (spliceS q t, a)
      tty -> do
        a <- eval (env cxt) <$> freshMeta cxt SObj Zero
        unifyCatch cxt tty (VLift Omega a)
        pure (spliceS Omega t, a)
  P.Pi x q i s' a b -> do
    checkBinderMode cxt s' q
    when (s' == SObj && marker cxt /= Present) (elabError cxt $ InsufficientMode)
    a <- checkIn cxt s' (stageMode s') a (VU s')
    b <- checkIn (bind cxt x s' (stageMode s') (eval (env cxt) a)) s' (stageMode s') b (VU s')
    pure (Pi x s' q i a b, VU s')
  P.Let x s' q a t u -> do
    checkBinderMode cxt s' q
    a <- checkIn cxt s' (stageMode s') a (VU s')
    let ~va = eval (env cxt) a
    t <- checkIn cxt s' q t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x s' q vt va) s u
    pure (Let x s' q a t u, b)
  P.Hole -> do
    a <- eval (env cxt) <$> freshMeta cxt s (stageMode s)
    t <- freshMeta cxt s Omega
    pure (t, a)
