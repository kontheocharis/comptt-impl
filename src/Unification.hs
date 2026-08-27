module Unification (unify) where

import Common
import Control.Exception
import Control.Monad (when)
import Data.IORef
import qualified Data.IntMap as IM
import Errors
import Evaluation
import Metacontext
import Syntax
import Value

-- Unification
--------------------------------------------------------------------------------

-- @@Todo: pruning

data Renamed
  = RenDirect Lvl
  | RenSpliced Lvl Mode -- mode of the splice's lift type
  | RenQuoted Lvl Mode Mode -- (mode of the source object binder, mode of the quote's lift type)
  deriving (Show)

-- | partial renaming from Γ to Δ
data PartialRenaming = PRen
  { -- | size of Γ
    dom :: Lvl,
    -- | size of Δ
    cod :: Lvl,
    -- | Whether # ∈ Γ
    domMrk :: Marker,
    -- | mapping from Δ vars to Γ vars
    ren :: IM.IntMap Renamed
  }
  deriving (Show)

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, i x : A[σ]) (Δ, i x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod domMrk ren) =
  PRen (dom + 1) (cod + 1) domMrk (IM.insert (unLvl cod) (RenDirect dom) ren)

-- | Lifting a partial renaming over an erasure marker variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, #) (Δ, #))
liftMarker :: PartialRenaming -> PartialRenaming
liftMarker (PRen dom cod domMd ren) =
  PRen dom cod Present ren

data Binder
  = BObj Mode Icit
  | BMeta Icit

-- | invert : (Γ : Cxt) → # ∈ Γ → Sub Γ Δ → PRen Δ Γ
--   Also returns the binders of the inverted spine, in spine order.
invert :: Lvl -> Marker -> Spine -> IO (PartialRenaming, [Binder])
invert gamma mrk sp = do
  let bind :: Lvl -> IM.IntMap Renamed -> [Binder] -> Binder -> Lvl -> Renamed -> IO (Lvl, IM.IntMap Renamed, [Binder])
      bind dom ren bs b (Lvl x) r
        | IM.notMember x ren = pure (dom + 1, IM.insert x r ren, bs :> b)
        | otherwise = throwIO InversionNonLinear

      go :: Spine -> IO (Lvl, IM.IntMap Renamed, [Binder])
      go [] = pure (0, mempty, [])
      go (_ :> ESplice _) = throwIO InversionNonVariables
      go (sp :> EAppObj t q i) = do
        (dom, ren, bs) <- go sp
        case force t of
          VVarObj x _ -> bind dom ren bs (BObj q i) x (RenDirect dom)
          VRigidMeta x [ESplice sq] -> bind dom ren bs (BObj q i) x (RenQuoted dom q sq)
          _ -> throwIO InversionNonVariables
      go (sp :> EAppMeta t i) = do
        (dom, ren, bs) <- go sp
        case force t of
          VQuote q t' -> case force t' of
            VVarObj x _ -> bind dom ren bs (BMeta i) x (RenSpliced dom q)
            _ -> throwIO InversionNonVariables
          VVarMeta x -> bind dom ren bs (BMeta i) x (RenDirect dom)
          _ -> throwIO InversionNonVariables

  (dom, ren, bs) <- go sp
  pure (PRen dom gamma mrk ren, bs)

-- | rename : (m : Meta i Δ) → PRen Δ Γ → Val Γ → Tm Δ
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v
  where
    goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
    goSp pren t [] = pure t
    goSp pren t (sp :> EAppObj u q i) = case q of
      Omega -> AppObj <$> goSp pren t sp <*> go pren u <*> pure q <*> pure i
      -- Every time we see a ↓, we must bind a #
      Zero -> AppObj <$> goSp pren t sp <*> go (liftMarker pren) u <*> pure q <*> pure i
    goSp pren t (sp :> EAppMeta u i) =
      AppMeta <$> goSp pren t sp <*> go pren u <*> pure i
    goSp pren t (sp :> ESplice q) = do
      when (q == Zero) (encounterU pren)
      spliceS q <$> goSp pren t sp

    goVar :: PartialRenaming -> Int -> Spine -> IO Tm
    goVar pren x sp = case IM.lookup x (ren pren) of
      Nothing -> throwIO Escaping
      Just (RenDirect x') ->
        goSp pren (Var (lvl2Ix (dom pren) x')) sp
      Just (RenSpliced x' q) -> do
        when (q == Zero) (encounterU pren)
        goSp pren (spliceS q (Var (lvl2Ix (dom pren) x'))) sp
      Just (RenQuoted x' bq sq) -> do
        when (bq == Zero && sq == Omega) (encounterU pren)
        goSp pren (quoteS sq (Var (lvl2Ix (dom pren) x'))) sp

    -- Every time we see a ↑, we must check that # ∈ Γ
    encounterU :: PartialRenaming -> IO ()
    encounterU pren = case (domMrk pren) of
      Absent -> throwIO EscapingMarker
      Present -> pure ()

    go :: PartialRenaming -> Val -> IO Tm
    go pren t = case force t of
      VFlex m' mrk sp
        | m == m' -> throwIO Occurs
        | otherwise -> do
            when (mrk == Present) (encounterU pren)
            goSp pren (Meta m' mrk) sp
      VRigidObj (Lvl x) md sp -> do
        when (md == Zero) (encounterU pren)
        goVar pren x sp
      VRigidMeta (Lvl x) sp -> goVar pren x sp
      VLamObj x q i t ->
        LamObj x q i <$> go (lift pren) (t $$ VVarObj (cod pren) q)
      VLamMeta x i t ->
        LamMeta x i <$> go (lift pren) (t $$ VVarMeta (cod pren))
      VPiObj x q i r a b -> do
        encounterU pren
        PiObj x q i <$> go pren r <*> go pren a <*> go (lift pren) (b $$ VVarObj (cod pren) Zero)
      VPiMeta x i a b ->
        PiMeta x i <$> go pren a <*> go (lift pren) (b $$ VVarMeta (cod pren))
      VProducer a -> do
        encounterU pren
        Producer <$> go pren a
      VRet t -> Ret <$> go pren t
      VUMeta -> pure UMeta
      VUObj th a -> do
        encounterU pren
        UObj <$> go pren th <*> go pren a
      VLift q a -> Lift q <$> go (liftMarker pren) a
      VQuote q t -> case q of
        Omega -> quoteS q <$> go pren t
        Zero -> quoteS q <$> go (liftMarker pren) t
      VPolU -> pure PolU
      VPol p -> pure (Pol p)
      VRepU th -> RepU <$> go pren th
      VRep r -> Rep <$> bitraverseRepF (go pren) (go pren) r

lams :: [Binder] -> Tm -> Tm
lams = go (0 :: Int)
  where
    go _ [] t = t
    go x (BObj q i : bs) t = LamObj (name x) q i (go (x + 1) bs t)
    go x (BMeta i : bs) t = LamMeta (name x) i (go (x + 1) bs t)
    name x = "x" ++ show (x + 1)

-- (For the 'NotDowned' case:)
-- solve : (Γ : Con) → (m : Meta i Δ) -> # ∈ Δ → Sub Γ Δ → Tm Γ → TC ()
solve :: Lvl -> MetaVar -> Marker -> Spine -> Val -> IO ()
solve gamma m mrk sp rhs = do
  (pren, binders) <- invert gamma mrk sp
  rhs <- rename m pren rhs
  let solution = eval [] $ lams (reverse binders) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved mrk solution)

unifyRepF :: Lvl -> RepF Val Val -> RepF Val Val -> IO ()
unifyRepF l r r' = case (r, r') of
  (RUnit th, RUnit th') -> unify l th th'
  (RProducer a, RProducer a') -> unify l a a'
  (RArrow a b, RArrow a' b') -> unify l a a' >> unify l b b'
  _ -> throwIO UnifyError

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([], []) -> pure ()
  (sp :> EAppObj t q _, sp' :> EAppObj t' q' _) | q == q' -> unifySp l sp sp' >> unify l t t'
  (sp :> EAppMeta t _, sp' :> EAppMeta t' _) -> unifySp l sp sp' >> unify l t t'
  (sp :> ESplice q, sp' :> ESplice q') | q == q' -> unifySp l sp sp'
  _ -> throwIO UnifyError

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLamObj _ q _ t, VLamObj _ q' _ t')
    | q == q' -> unify (l + 1) (t $$ VVarObj l q) (t' $$ VVarObj l q)
    | otherwise -> throwIO UnifyError
  (VLamMeta _ _ t, VLamMeta _ _ t') -> unify (l + 1) (t $$ VVarMeta l) (t' $$ VVarMeta l)
  (VFlex m _ sp, VFlex m' _ sp')
    | m == m' -> unifySp l sp sp'
  -- @@Todo: apply full η expansion
  (VFlex m mrk (sp :> ESplice q), t') -> solve l m mrk sp (vQuote q t')
  (t, VFlex m' mrk (sp' :> ESplice q)) -> solve l m' mrk sp' (vQuote q t)
  (t, VLamObj _ q i b) -> unify (l + 1) (vAppObj t (VVarObj l q) q i) (b $$ VVarObj l q)
  (t, VLamMeta _ i b) -> unify (l + 1) (vAppMeta t (VVarMeta l) i) (b $$ VVarMeta l)
  (VLamObj _ q i b, u) -> unify (l + 1) (b $$ VVarObj l q) (vAppObj u (VVarObj l q) q i)
  (VLamMeta _ i b, u) -> unify (l + 1) (b $$ VVarMeta l) (vAppMeta u (VVarMeta l) i)
  (VProducer a, VProducer a') -> unify l a a'
  (VRet t, VRet t') -> unify l t t'
  (VUMeta, VUMeta) -> pure ()
  (VUObj th a, VUObj th' a') -> unify l th th' >> unify l a a'
  (VPolU, VPolU) -> pure ()
  (VPol p, VPol p') | p == p' -> pure ()
  (VRepU th, VRepU th') -> unify l th th'
  (VRep r, VRep r') -> unifyRepF l r r'
  (VPiObj x q i r a b, VPiObj x' q' i' r' a' b')
    | q == q' && i == i' ->
        unify l r r' >> unify l a a' >> unify (l + 1) (b $$ VVarObj l Zero) (b' $$ VVarObj l Zero)
  (VPiMeta x i a b, VPiMeta x' i' a' b')
    | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVarMeta l) (b' $$ VVarMeta l)
  (VLift q a, VLift q' a') | q == q' -> unify l a a'
  (VQuote q t, VQuote q' t') | q == q' -> unify l t t'
  (VQuote q t, t') -> unify l t (vSplice q t')
  (t, VQuote q t') -> unify l (vSplice q t) t'
  (VRigidObj x _ sp, VRigidObj x' _ sp')
    | x == x' -> unifySp l sp sp'
  (VRigidMeta x sp, VRigidMeta x' sp')
    | x == x' -> unifySp l sp sp'
  (VFlex m mrk sp, t') -> solve l m mrk sp t'
  (t, VFlex m' mrk sp') -> solve l m' mrk sp' t
  _ -> throwIO UnifyError
