module Common
  ( module Common,
    SourcePos (..),
    Pos,
    unPos,
    initialPos,
  )
where

import Text.Megaparsec

type Name = String

-- Annotates terms and binders
-- i ∈ {0, ω}
data Mode = Zero | Omega deriving (Eq)

-- Object or meta level of the 2LTT
data Stage = SObj | SMeta deriving (Eq)

-- CBPV polarisation: positive = values, negative = computations
data Polarity = Pos | Neg deriving (Eq)

-- Functor for representations
data RepF p a
  = RUnit p
  | RProducer a
  | RArrow a a
  deriving (Show, Functor, Foldable, Traversable)

bimapRepF :: (p -> q) -> (a -> b) -> RepF p a -> RepF q b
bimapRepF f g = \case
  RUnit p -> RUnit (f p)
  RProducer a -> RProducer (g a)
  RArrow a b -> RArrow (g a) (g b)

bitraverseRepF :: (Applicative f) => (p -> f q) -> (a -> f b) -> RepF p a -> f (RepF q b)
bitraverseRepF f g = \case
  RUnit p -> RUnit <$> f p
  RProducer a -> RProducer <$> g a
  RArrow a b -> RArrow <$> g a <*> g b

-- The erasure mode for types in a given stage.
-- Here `Omega` really means "erasure phase not necessary".
stageTypeMode :: Stage -> Mode
stageTypeMode SObj = Zero
stageTypeMode SMeta = Omega

-- The free meet-semilattice on {#, $} which appear in contexts. Phase itself is
-- representable because representable types are closed under products and unit.
--
--   Tm ω (Γ, #) ≅ Tm 0 Γ
--   Tm ω (Γ, $) ≅ Ex Γ
data Phase = Phase {erasure :: Bool, compilation :: Bool} deriving (Eq, Show)

topPhase :: Phase
topPhase = Phase False False

erasurePhase :: Phase
erasurePhase = Phase True False

modePhase :: Mode -> Phase
modePhase Zero = erasurePhase
modePhase Omega = topPhase

compilationPhase :: Phase
compilationPhase = Phase False True

botPhase :: Phase
botPhase = Phase True True

meetPhase :: Phase -> Phase -> Phase
meetPhase (Phase e c) (Phase e' c') = Phase (e || e') (c || c')

-- assuming ph is at least as strong as assuming ph'
entails :: Phase -> Phase -> Bool
entails ph ph' = meetPhase ph ph' == ph

phaseMarkerNames :: Phase -> [String]
phaseMarkerNames (Phase e c) = ["erasure marker" | e] ++ ["compilation marker" | c]

----

data Icit = Impl | Expl deriving (Eq)

data BD = Bound Stage Mode | Defined deriving (Show)

instance Show Mode where
  show Zero = "0"
  show Omega = "ω"

instance Show Stage where
  show SObj = "obj"
  show SMeta = "meta"

instance Show Polarity where
  show Pos = "+"
  show Neg = "-"

instance Show Icit where
  show Impl = "implicit"
  show Expl = "explicit"

-- | De Bruijn index.
newtype Ix = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

ix2Lvl :: Lvl -> Ix -> Lvl
ix2Lvl (Lvl l) (Ix x) = Lvl (l - x - 1)

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>

pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- x : xs where (:>) xs ~x = x : xs

{-# COMPLETE (:>), [] #-}
