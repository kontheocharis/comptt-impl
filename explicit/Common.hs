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

-- Erasure marker (#), appears in contexts:
-- Tm ω (Γ, #) ≃ Tm 0 Γ
data Marker = Present | Absent deriving (Eq, Show)

ext :: Marker -> Marker -> Marker
ext Present _ = Present
ext _ Present = Present
ext Absent Absent = Absent

-- Conversion functions between Mode and Marker

getMode :: Marker -> Mode
getMode Present = Zero
getMode Absent = Omega

getMarker :: Mode -> Marker
getMarker Zero = Present
getMarker Omega = Absent

-- Movement ↑/↓ between modes

data Dir = Upward | Downward deriving (Eq, Show)

invertDir :: Dir -> Dir
invertDir Upward = Downward
invertDir Downward = Upward

-- Helpers to track ↑/↓ switches

data IsUpped = YesUpped | NotUpped
  deriving (Eq, Show)

data IsDowned = YesDowned | NotDowned
  deriving (Eq, Show)

moveIsUpped :: Dir -> IsUpped -> IsUpped
moveIsUpped Upward NotUpped = YesUpped
moveIsUpped Upward YesUpped = error "impossible"
moveIsUpped Downward YesUpped = NotUpped
moveIsUpped Downward NotUpped = error "impossible"

moveIsDowned :: Dir -> IsDowned -> IsDowned
moveIsDowned Upward NotDowned = error "impossible"
moveIsDowned Upward YesDowned = NotDowned
moveIsDowned Downward NotDowned = YesDowned
moveIsDowned Downward YesDowned = error "impossible"

ifIsUpped :: (a -> a) -> IsUpped -> a -> a
ifIsUpped f NotUpped = id
ifIsUpped f YesUpped = f

ifIsDowned :: (a -> a) -> IsDowned -> a -> a
ifIsDowned f NotDowned = id
ifIsDowned f YesDowned = f

fromZero :: Mode -> Maybe Dir
fromZero Zero = Nothing
fromZero Omega = Just Upward

downToZero :: Mode -> IsDowned
downToZero Zero = NotDowned
downToZero Omega = YesDowned

----

data Icit = Impl | Expl deriving (Eq)

data BD = Bound Mode | Defined deriving (Show)

instance Show Mode where
  show Zero = "0"
  show Omega = "ω"

instance Show Icit where
  show Impl = "implicit"
  show Expl = "explicit"

-- | De Bruijn index.
newtype Ix = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>

pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- x : xs where (:>) xs ~x = x : xs

{-# COMPLETE (:>), [] #-}
