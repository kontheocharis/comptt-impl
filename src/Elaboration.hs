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

-- @@Todo: TC postponing!

freshMeta :: Cxt -> Stage -> Mode -> VTy -> IO Tm
freshMeta cxt s q ~a = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  let mrk = marker (withMarker s q cxt)
  modifyIORef' mcxt $ IM.insert m (Unsolved mrk (eval [] (closeTy cxt a)))
  pure (InsertedMeta (MetaVar m) mrk (bds cxt))

freshMetaVal :: Cxt -> Stage -> Mode -> VTy -> IO Val
freshMetaVal cxt s q ~a = eval (env cxt) <$> freshMeta cxt s q a

freshPol :: Cxt -> IO Tm
freshPol cxt = freshMeta cxt SMeta Omega VPolU

freshRep :: Cxt -> VPol -> IO Tm
freshRep cxt th = freshMeta cxt SMeta Omega (VRepU th)

freshRepVal :: Cxt -> VPol -> IO Val
freshRepVal cxt th = freshMetaVal cxt SMeta Omega (VRepU th)

freshPolVal :: Cxt -> IO Val
freshPolVal cxt = freshMetaVal cxt SMeta Omega VPolU

freshUniverse :: Cxt -> Stage -> IO VTy
freshUniverse _ SMeta = pure VUMeta
freshUniverse cxt SObj = do
  th <- freshPolVal cxt
  VUObj th <$> freshRepVal cxt th

freshTypeVal :: Cxt -> Stage -> IO VTy
freshTypeVal cxt s = eval (env cxt) <$> freshType cxt s

freshType :: Cxt -> Stage -> IO Ty
freshType cxt s = do
  u <- freshUniverse (withMarker s (stageTypeMode s) cxt) s
  freshMeta cxt s (stageTypeMode s) u

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
      va | Just (x, s, q, Impl, a, b) <- viewPi va -> do
        m <- freshMeta cxt s q a
        let mv = eval (env cxt) m
        go (mkApp t m s q Impl, b $$ mv)
      va -> pure (t, va)

mkLam :: Name -> Stage -> Mode -> Icit -> Ty -> Tm -> Tm
mkLam x SObj q i a = LamObj x q i a
mkLam x SMeta _ i a = LamMeta x i a

mkApp :: Tm -> Tm -> Stage -> Mode -> Icit -> Tm
mkApp t u SObj q i = AppObj t u q i
mkApp t u SMeta _ i = AppMeta t u i

isImplLam :: Tm -> Bool
isImplLam = \case
  LamObj _ _ Impl _ _ -> True
  LamMeta _ Impl _ _ -> True
  _ -> False

insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act =
  act >>= \case
    (t, va) | isImplLam t -> pure (t, va)
    (t, va) -> insert' cxt (pure (t, va))

insertUntilName :: Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act
  where
    go (t, va) = case force va of
      va | Just (x, s, q, Impl, a, b) <- viewPi va -> do
        if x == name
          then
            pure (t, va)
          else do
            m <- freshMeta cxt s q a
            let mv = eval (env cxt) m
            go (mkApp t m s q Impl, b $$ mv)
      _ -> elabError cxt $ NoNamedImplicitArg name

withMarker :: Stage -> Mode -> Cxt -> Cxt
withMarker SObj Zero = enterMarker
withMarker _ _ = id

-- Check in a given mode and stage
--
-- check : (Γ : Ctx) -> (s : {meta, obj}) -> (i : {0, ω}) -> PTm -> Tyₛ Γ -> TC (Tmₛ {i} A)
checkIn :: Cxt -> Stage -> Mode -> P.Tm -> VTy -> IO Tm
checkIn cxt s q t a = check (withMarker s q cxt) s t a

-- Check whether the given mode on a binder is valid in the given stage. We
-- default to `runtime` mode for meta-binders, which is easier than some kind of
-- mutually-exclusive pair of optional values.
checkBinderMode :: Cxt -> Stage -> Mode -> IO ()
checkBinderMode cxt SMeta Zero = elabError cxt ErasedMetaBinder
checkBinderMode _ _ _ = pure ()

ensureStage :: Cxt -> Stage -> Stage -> IO ()
ensureStage cxt s s' = when (s /= s') (elabError cxt $ StageMismatch s s')

ensureMode :: Cxt -> Mode -> IO ()
ensureMode cxt Zero = when (marker cxt /= Present) (elabError cxt InsufficientMode)
ensureMode _ Omega = pure ()

checkType :: Cxt -> Stage -> P.Tm -> IO Tm
checkType cxt s a = do
  u <- freshUniverse (withMarker s (stageTypeMode s) cxt) s
  checkIn cxt s (stageTypeMode s) a u

checkRep :: Cxt -> Polarity -> P.Tm -> IO Tm
checkRep cxt th a = check cxt SMeta a (VRepU (VPol th))

-- Potentially coerce a term of an inferred type, to match the expected type.
coerce :: Cxt -> Tm -> VTy -> VTy -> IO Tm
coerce cxt t inferred expected = case (force expected, force inferred) of
  (VProducer a, i) | yieldsValue i -> do
    unifyCatch cxt a i
    pure (Ret t)
  _ -> do
    unifyCatch cxt expected inferred
    pure t
  where
    yieldsValue = \case
      VProducer {} -> False
      VFlex {} -> False
      _ -> True

-- Check in mode ω (default)
check :: Cxt -> Stage -> P.Tm -> VTy -> IO Tm
check cxt s t a = case (t, force a) of
  (P.SrcPos pos t, a) ->
    check (cxt {pos = pos}) s t a
  (P.Lam x i t, viewPi -> Just (x', s', q', i', a, b)) | either (\x -> x == x' && i' == Impl) (== i') i -> do
    -- Here we must wrap the variable in ↓ if the q = ω, because of the lambda rule.
    mkLam x s' q' i' (quote (lvl cxt) a) <$> check (bind cxt x s' q' a) s' t (b $$ vVar (lvl cxt) s' q' a)
  (t, viewPi -> Just (x, s', q, Impl, a, b)) -> do
    mkLam x s' q Impl (quote (lvl cxt) a) <$> check (newBinder cxt x s' q a) s' t (b $$ vVar (lvl cxt) s' q a)
  (P.Let x s' q a t u, a') -> do
    checkBinderMode cxt s' q
    a <- checkType cxt s' a
    let ~va = eval (env cxt) a
    t <- checkIn cxt s' q t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x s' q vt va) s u a'
    pure (Let x s' q a t u)
  (P.Ret t, VProducer a) ->
    Ret <$> check cxt s t a
  (P.Quote t, VLift q a) -> do
    ensureStage cxt s SMeta
    quoteS q <$> checkIn cxt SObj q t a
  (P.Hole, a) ->
    freshMeta cxt s Omega a
  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt s t
    coerce cxt t inferred expected

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
              ensureStage cxt s s'
              ensureMode cxt q
              pure (Var ix, a)
          | otherwise = go (ix + 1) types
        go ix [] =
          elabError cxt $ NameNotInScope x
    go 0 (types cxt)
  P.Lam _ (Right _) _ | s == SObj -> elabError cxt InferObjLam
  P.Lam x (Right i) t -> do
    -- By default infer a runtime lambda
    let q = Omega
    a <- freshType cxt s
    let ~va = eval (env cxt) a
    let cxt' = bind cxt x s q va
    (t, b) <- insert cxt' $ infer cxt' s t
    pure (LamMeta x i a t, VPiMeta x i va $ closeVal cxt b)
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
      tty | Just (x, s', q, i', a, b) <- viewPi tty -> do
        unless (i == i') $ elabError cxt $ IcitMismatch i i'
        pure (s', q, a, b)
      tty -> do
        let q = Omega
        a <- freshTypeVal cxt s
        let cxt' = bind cxt "x" s q a
        b <- Closure (env cxt) <$> freshType cxt' s
        expected <- case s of
          SMeta -> pure (VPiMeta "x" i a b)
          SObj -> (\r -> VPiObj "x" q i r a b) <$> freshRepVal cxt (VPol Neg)
        unifyCatch cxt expected tty
        pure (s, q, a, b)

    u <- checkIn cxt s' q u a
    pure (mkApp t u s' q i, b $$ eval (env cxt) u)
  P.UMeta -> do
    ensureStage cxt s SMeta
    pure (UMeta, VUMeta)
  P.UObj r -> do
    ensureStage cxt s SObj
    ensureMode cxt Zero
    -- We can deduce the polarity from r
    th <- freshPol cxt
    a <- check cxt SMeta r (VRepU (eval (env cxt) th))
    pure (UObj th a, VUObj (VPol Pos) vUnitRep)
  P.Producer a -> do
    ensureStage cxt s SObj
    ensureMode cxt Zero
    rep <- freshRepVal cxt (VPol Pos)
    a <- checkIn cxt SObj Zero a (VUObj (VPol Pos) rep)
    pure (Producer a, VUObj (VPol Neg) (VRep (RProducer rep)))
  P.Ret t -> do
    ensureStage cxt s SObj
    (t, a) <- infer cxt s t
    pure (Ret t, VProducer a)
  P.Lift q a -> do
    ensureStage cxt s SMeta
    a <- checkType cxt SObj a
    pure (Lift q a, VUMeta)
  P.PolU -> do
    ensureStage cxt s SMeta
    pure (PolU, VUMeta)
  P.Pol th -> do
    ensureStage cxt s SMeta
    pure (Pol th, VPolU)
  P.RepU th -> do
    ensureStage cxt s SMeta
    th <- check cxt SMeta th VPolU
    pure (RepU th, VUMeta)
  P.Rep (RUnit th) -> do
    ensureStage cxt s SMeta
    th <- check cxt SMeta th VPolU
    pure (Rep (RUnit th), VRepU (eval (env cxt) th))
  P.Rep (RProducer a) -> do
    ensureStage cxt s SMeta
    a <- checkRep cxt Pos a
    pure (Rep (RProducer a), VRepU (VPol Neg))
  P.Rep (RArrow a b) -> do
    ensureStage cxt s SMeta
    a <- checkRep cxt Pos a
    b <- checkRep cxt Neg b
    pure (Rep (RArrow a b), VRepU (VPol Neg))
  P.Quote t -> do
    ensureStage cxt s SMeta
    (t, a) <- inferIn cxt SObj Omega t
    pure (quoteS Omega t, VLift Omega a)
  P.Splice t -> do
    ensureStage cxt s SObj
    (t, tty) <- infer cxt SMeta t
    case force tty of
      VLift q a -> do
        ensureMode cxt q
        pure (spliceS q t, a)
      tty -> do
        a <- freshTypeVal cxt SObj
        unifyCatch cxt (VLift Omega a) tty
        pure (spliceS Omega t, a)
  P.Pi x q i SMeta a b -> do
    ensureStage cxt s SMeta
    checkBinderMode cxt SMeta q
    a <- checkIn cxt SMeta Omega a VUMeta
    b <- checkIn (bind cxt x SMeta Omega (eval (env cxt) a)) SMeta Omega b VUMeta
    pure (PiMeta x i a b, VUMeta)
  P.Pi x q i SObj a b -> do
    ensureStage cxt s SObj
    ensureMode cxt Zero
    let ev = eval (env cxt)
    codTh <- freshPol cxt
    codRep <- freshRep cxt (ev codTh)
    let checkCod a = checkIn (bind cxt x SObj Zero (ev a)) SObj Zero b (VUObj (ev codTh) (ev codRep))
    case q of
      -- ω-domain pi has the arrow representation
      -- 0-domain pi has the representation of its codomain
      Omega -> do
        domRep <- freshRep cxt (VPol Pos)
        a <- checkIn cxt SObj Zero a (VUObj (VPol Pos) (ev domRep))
        b <- checkCod a
        (b, codRep) <- case force (ev codTh) of
          -- Here we try to insert a ▶ if needed.
          VPol Pos -> pure (Producer b, Rep (RProducer codRep))
          _ -> do
            unifyCatch cxt (VPol Neg) (ev codTh)
            pure (b, codRep)
        let r = Rep (RArrow domRep codRep)
        pure (PiObj x Omega i r a b, VUObj (VPol Neg) (ev r))
      Zero -> do
        domTh <- freshPol cxt
        domRep <- freshRep cxt (ev domTh)
        a <- checkIn cxt SObj Zero a (VUObj (ev domTh) (ev domRep))
        b <- checkCod a
        pure (PiObj x Zero i codRep a b, VUObj (ev codTh) (ev codRep))
  P.Let x s' q a t u -> do
    checkBinderMode cxt s' q
    a <- checkType cxt s' a
    let ~va = eval (env cxt) a
    t <- checkIn cxt s' q t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x s' q vt va) s u
    pure (Let x s' q a t u, b)
  P.Hole -> do
    a <- freshTypeVal cxt s
    t <- freshMeta cxt s Omega a
    pure (t, a)
