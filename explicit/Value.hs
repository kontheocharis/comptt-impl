module Value where

import Common
import Syntax

type Env = [Val]

type Spine = [(Val, Mode, Icit)]

data Closure
  = Closure
      Env
      Tm
      IsDowned -- whether Tm applies an extra ↓ to its argument that we must offset (see Elaboration)
  deriving (Show)

type VTy = Val

-- Each value is marked by whether it is coerced. There is only one possible
-- coercion per value.
data Val
  = VFlex IsDowned MetaVar Marker Spine
  | VRigid IsDowned IsUpped Lvl Spine
  | VLam' IsDowned Name Mode Icit {-# UNPACK #-} Closure
  | VPi' IsUpped Name Mode Icit ~VTy {-# UNPACK #-} Closure
  | VU' IsUpped
  deriving (Show)

-- Patterns for uncoerced values
pattern VLam :: Name -> Mode -> Icit -> Closure -> Val
pattern VLam x q i t = VLam' NotDowned x q i t

pattern VPi :: Name -> Mode -> Icit -> VTy -> Closure -> Val
pattern VPi x q i a b = VPi' NotUpped x q i a b

pattern VU :: Val
pattern VU = VU' NotUpped

-- Pattern for variables x0 or xω
pattern VVar :: Lvl -> Mode -> Val
pattern VVar x m <- (matchVVar -> Just (m, x))
  where
    VVar x Zero = VRigid YesDowned YesUpped x []
    VVar x Omega = VRigid NotDowned NotUpped x []

matchVVar :: Val -> Maybe (Mode, Lvl)
matchVVar (VRigid YesDowned YesUpped x []) = Just (Zero, x)
matchVVar (VRigid NotDowned NotUpped x []) = Just (Omega, x)
matchVVar _ = Nothing

pattern VMeta :: MetaVar -> Marker -> Val
pattern VMeta m mrk = VFlex NotDowned m mrk []

-- Pattern for variables ↑x0, ↓xω, and x0/xω
pattern VWrappedVar :: Lvl -> Maybe Dir -> Val
pattern VWrappedVar mw dir <- (matchVWrappedVar -> Just (mw, dir))
  where
    VWrappedVar x Nothing = VRigid YesDowned YesUpped x []
    VWrappedVar x (Just Upward) = VRigid YesDowned NotUpped x []
    VWrappedVar x (Just Downward) = VRigid NotDowned YesUpped x []

matchVWrappedVar :: Val -> Maybe (Lvl, Maybe Dir)
matchVWrappedVar (VRigid YesDowned YesUpped x []) = Just (x, Nothing)
matchVWrappedVar (VRigid YesDowned NotUpped x []) = Just (x, Just Downward)
matchVWrappedVar (VRigid NotDowned NotUpped x []) = Just (x, Nothing)
matchVWrappedVar (VRigid NotDowned YesUpped x []) = Just (x, Just Upward)
matchVWrappedVar _ = Nothing
