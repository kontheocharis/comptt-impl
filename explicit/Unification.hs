module Unification (unify) where

import Common
import Control.Exception
import Control.Monad (when)
import Data.IORef
import qualified Data.IntMap as IM
import Data.Maybe (fromMaybe)
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
    ren :: IM.IntMap (Lvl, Maybe Dir)
  }
  deriving (Show)

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, i x : A[σ]) (Δ, i x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod domMd ren) =
  PRen (dom + 1) (cod + 1) domMd (IM.insert (unLvl cod) (dom, Nothing) ren)

-- | Lifting a partial renaming over an erasure marker variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, #) (Δ, #))
liftMarker :: PartialRenaming -> PartialRenaming
liftMarker (PRen dom cod domMd ren) =
  PRen dom cod Present ren

-- | invert : (Γ : Cxt) → # ∈ Γ → Sub Γ Δ → PRen Δ Γ
invert :: Lvl -> Marker -> Spine -> IO PartialRenaming
invert gamma mrk sp = do
  let go :: Spine -> IO (Lvl, IM.IntMap (Lvl, Maybe Dir))
      go [] = pure (0, mempty)
      go (sp :> (t, _, _)) = do
        (dom, ren) <- go sp
        case force t of
          VWrappedVar (Lvl x) d ->
            if IM.notMember x ren
              then pure (dom + 1, IM.insert x (dom, invertDir <$> d) ren)
              else throwIO InversionNonLinear
          _ -> throwIO InversionNonVariables

  (dom, ren) <- go sp
  pure $ PRen dom gamma mrk ren

-- | rename : (m : Meta i Δ) → PRen Δ Γ → Val Γ → Tm Δ
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v
  where
    goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
    goSp pren t [] = pure t
    goSp pren t (sp :> (u, q, i)) = App <$> goSp pren t sp <*> go pren u <*> pure q <*> pure i

    -- Every time we see a ↓, we must bind a #
    enterD :: IsDowned -> PartialRenaming -> PartialRenaming
    enterD isd pren = ifIsDowned liftMarker isd pren

    -- Every time we see a ↑, we must check that # ∈ Γ
    encounterU :: PartialRenaming -> IsUpped -> IO ()
    encounterU pren isu = case (domMrk pren, isu) of
      (Absent, YesUpped) -> throwIO EscapingMarker
      _ -> pure ()

    go :: PartialRenaming -> Val -> IO Tm
    go pren t = case force t of
      VFlex isd m' mrk sp
        | m == m' -> throwIO Occurs
        | otherwise -> do
            when (mrk == Present) (encounterU (enterD isd pren) YesUpped)
            quoteD isd <$> goSp (enterD isd pren) (Meta m' mrk) sp
      VRigid isd isu (Lvl x) sp -> do
        when (isd == NotDowned) (encounterU pren isu) -- check up arrow validity
        case IM.lookup x (ren pren) of
          Nothing -> throwIO Escaping
          Just (x', dir) -> do
            -- Substitute the variable, adjusting for any ↑/↓ differences
            let newVarIsU = fromMaybe isu (moveIsUpped <$> dir <*> pure isu)
            quoteD isd <$> goSp (enterD isd pren) (quoteU newVarIsU $ Var (lvl2Ix (dom pren) x')) sp
      VLam' isd x q i t ->
        quoteD isd <$> Lam x q i <$> go (enterD isd (lift pren)) (t $$ VVar (cod pren) q)
      VPi' isu x q i a b -> do
        encounterU pren isu
        quoteU isu <$> (Pi x q i <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren) Zero))
      VU' isu -> do
        encounterU pren isu
        pure $ quoteU isu U

lams :: [(Mode, Icit)] -> Tm -> Tm
lams = go (0 :: Int)
  where
    go x [] t = t
    go x ((q, i) : is) t = Lam ("x" ++ show (x + 1)) q i $ go (x + 1) is t

-- (For the 'NotDowned' case:)
-- solve : (Γ : Con) → (m : Meta i Δ) -> # ∈ Δ → Sub Γ Δ → Tm Γ → TC ()
solve :: Lvl -> MetaVar -> IsDowned -> Marker -> Spine -> Val -> IO ()
solve gamma m YesDowned mrk sp rhs = solve gamma m NotDowned mrk sp (up rhs)
solve gamma m NotDowned mrk sp rhs = do
  pren <- invert gamma mrk sp
  rhs <- rename m pren rhs
  let solution = eval [] $ lams (reverse $ map (\(_, q, i) -> (q, i)) sp) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved mrk solution)

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([], []) -> pure ()
  (sp :> (t, q, _), sp' :> (t', q', _)) | q == q' -> unifySp l sp sp' >> unify l t t'
  _ -> throwIO UnifyError

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLam' _ _ q _ t, VLam' _ _ q' _ t') -> unify (l + 1) (t $$ VVar l q) (t' $$ VVar l q')
  (t, VLam' isd _ q i t') -> unify (l + 1) (vApp (offsetD isd t) (VVar l q) q i) (t' $$ VVar l q)
  (VLam' isd _ q i t, t') -> unify (l + 1) (t $$ VVar l q) (vApp (offsetD isd t') (VVar l q) q i)
  (VU' _, VU' _) -> pure ()
  (VPi' _ x q i a b, VPi' isu' x' q' i' a' b')
    | q == q' && i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l Zero) (b' $$ VVar l Zero)
  (VRigid _ _ x sp, VRigid _ _ x' sp')
    | x == x' -> unifySp l sp sp'
  (VFlex _ m _ sp, VFlex _ m' _ sp')
    | m == m' -> unifySp l sp sp'
  (VFlex isd m mrk sp, t') -> solve l m isd mrk sp t'
  (t, VFlex isd m' mrk sp') -> solve l m' isd mrk sp' t
  _ -> throwIO UnifyError
