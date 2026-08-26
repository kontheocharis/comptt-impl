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

-- | partial renaming from Γ to Δ
data PartialRenaming = PRen
  { -- | size of Γ
    dom :: Lvl,
    -- | size of Δ
    cod :: Lvl,
    -- | Whether # ∈ Γ
    domMrk :: Marker,
    -- | mapping from Δ vars to Γ vars
    ren :: IM.IntMap (Lvl, Mode)
  }
  deriving (Show)

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, i x : A[σ]) (Δ, i x : A))
lift :: Mode -> PartialRenaming -> PartialRenaming
lift md (PRen dom cod domMrk ren) =
  PRen (dom + 1) (cod + 1) domMrk (IM.insert (unLvl cod) (dom, md) ren)

-- | Lifting a partial renaming over an erasure marker variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, #) (Δ, #))
liftMarker :: PartialRenaming -> PartialRenaming
liftMarker (PRen dom cod domMd ren) =
  PRen dom cod Present ren

-- | invert : (Γ : Cxt) → # ∈ Γ → Sub Γ Δ → PRen Δ Γ
--   Also returns the binders of the inverted spine, in spine order.
invert :: Lvl -> Marker -> Spine -> IO (PartialRenaming, [(Stage, Mode, Icit)])
invert gamma mrk sp = do
  let go :: Spine -> IO (Lvl, IM.IntMap (Lvl, Mode), [(Stage, Mode, Icit)])
      go [] = pure (0, mempty, [])
      go (_ :> ESplice _) = throwIO InversionNonVariables
      go (sp :> EApp t s q i) = do
        (dom, ren, bs) <- go sp
        case force t of
          VVar (Lvl x) md ->
            if IM.notMember x ren
              then pure (dom + 1, IM.insert x (dom, md) ren, bs :> (s, q, i))
              else throwIO InversionNonLinear
          _ -> throwIO InversionNonVariables

  (dom, ren, bs) <- go sp
  pure (PRen dom gamma mrk ren, bs)

-- | rename : (m : Meta i Δ) → PRen Δ Γ → Val Γ → Tm Δ
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v
  where
    goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
    goSp pren t [] = pure t
    goSp pren t (sp :> EApp u s q i) = case q of
      Omega -> App <$> goSp pren t sp <*> go pren u <*> pure s <*> pure q <*> pure i
      -- Every time we see a ↓, we must bind a #
      Zero -> App <$> goSp pren t sp <*> go (liftMarker pren) u <*> pure s <*> pure q <*> pure i
    goSp pren t (sp :> ESplice q) = do
      when (q == Zero) (encounterU pren)
      spliceS q <$> goSp pren t sp

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
      VRigid (Lvl x) md sp -> do
        when (md == Zero) (encounterU pren) -- check up arrow validity
        case IM.lookup x (ren pren) of
          Nothing -> throwIO Escaping
          Just (x', md) -> do
            -- Substitute the variable, adjusting for any ↑/↓ differences
            goSp pren (Var (lvl2Ix (dom pren) x') md) sp
      VLam x s q i t ->
        Lam x s q i <$> go (lift q pren) (t $$ VVar (cod pren) q)
      VPi x s q i a b -> do
        encounterU pren
        (Pi x s q i <$> go pren a <*> go (lift (stageMode s) pren) (b $$ VVar (cod pren) (stageMode s)))
      VU s -> do
        encounterU pren
        pure (U s)
      VLift q a -> Lift q <$> go (liftMarker pren) a
      VQuote q t -> case q of
        Omega -> quoteS q <$> go pren t
        Zero -> quoteS q <$> go (liftMarker pren) t

lams :: [(Stage, Mode, Icit)] -> Tm -> Tm
lams = go (0 :: Int)
  where
    go x [] t = t
    go x ((s, q, i) : is) t = Lam ("x" ++ show (x + 1)) s q i $ go (x + 1) is t

-- (For the 'NotDowned' case:)
-- solve : (Γ : Con) → (m : Meta i Δ) -> # ∈ Δ → Sub Γ Δ → Tm Γ → TC ()
solve :: Lvl -> MetaVar -> Marker -> Spine -> Val -> IO ()
solve gamma m mrk sp rhs = do
  (pren, binders) <- invert gamma mrk sp
  rhs <- rename m pren rhs
  let solution = eval [] $ lams (reverse binders) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved mrk solution)

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([], []) -> pure ()
  (sp :> EApp t s q _, sp' :> EApp t' s' q' _) | s == s' && q == q' -> unifySp l sp sp' >> unify l t t'
  (sp :> ESplice q, sp' :> ESplice q') | q == q' -> unifySp l sp sp'
  _ -> throwIO UnifyError

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLam _ s q _ t, VLam _ s' q' _ t')
    | s == s' && q == q' -> unify (l + 1) (t $$ VVar l q) (t' $$ VVar l q')
    | otherwise -> throwIO UnifyError
  (VFlex m _ sp, VFlex m' _ sp')
    | m == m' -> unifySp l sp sp'
  (VFlex m mrk (sp :> ESplice q), t') -> solve l m mrk sp (vQuote q t')
  (t, VFlex m' mrk (sp' :> ESplice q)) -> solve l m' mrk sp' (vQuote q t)
  (t, VLam _ s q i t') -> unify (l + 1) (vApp t (VVar l q) s q i) (t' $$ VVar l q)
  (VLam _ s q i t, t') -> unify (l + 1) (t $$ VVar l q) (vApp t' (VVar l q) s q i)
  (VU s, VU s') | s == s' -> pure ()
  (VPi x s q i a b, VPi x' s' q' i' a' b')
    | s == s' && q == q' && i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l (stageMode s)) (b' $$ VVar l (stageMode s))
  (VLift q a, VLift q' a') | q == q' -> unify l a a'
  (VQuote q t, VQuote q' t') | q == q' -> unify l t t'
  (VQuote q t, t') -> unify l t (vSplice q t')
  (t, VQuote q t') -> unify l (vSplice q t) t'
  (VRigid x _ sp, VRigid x' _ sp')
    | x == x' -> unifySp l sp sp'
  (VFlex m mrk sp, t') -> solve l m mrk sp t'
  (t, VFlex m' mrk sp') -> solve l m' mrk sp' t
  _ -> throwIO UnifyError
