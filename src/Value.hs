module Value where

import Common
import Syntax

type Env = [Val]

data Elim
  = EAppObj Val Mode Icit
  | EAppMeta Val Icit
  | ESplice Mode
  deriving (Show)

type Spine = [Elim]

data Closure = Closure Env Tm deriving (Show)

type VTy = Val

type VRep = Val

type VPol = Val

data Val
  = VFlex MetaVar Marker Spine
  | VRigidObj Lvl Mode Spine -- records the original mode the variable was bound in
  | VRigidMeta Lvl Spine
  | VLamObj Name Mode Icit {-# UNPACK #-} Closure
  | VLamMeta Name Icit {-# UNPACK #-} Closure
  | VPiObj Name Mode Icit ~VRep ~VTy {-# UNPACK #-} Closure
  | VPiMeta Name Icit ~VTy {-# UNPACK #-} Closure
  | VProducer VTy
  | VRet Val
  | VUMeta
  | VUObj VPol VRep
  | VLift Mode VTy
  | VQuote Mode Val
  | VPolU
  | VPol Polarity
  | VRepU VPol
  | VRep (RepF VPol VRep)
  deriving (Show)

pattern VVarObj :: Lvl -> Mode -> Val
pattern VVarObj x m = VRigidObj x m []

pattern VVarMeta :: Lvl -> Val
pattern VVarMeta x = VRigidMeta x []

vVar :: Lvl -> Stage -> Mode -> Val
vVar x SObj q = VVarObj x q
vVar x SMeta _ = VVarMeta x

pattern VMeta :: MetaVar -> Marker -> Val
pattern VMeta m mrk = VFlex m mrk []

vUnitRep :: VRep
vUnitRep = VRep (RUnit (VPol Pos))

viewPi :: Val -> Maybe (Name, Stage, Mode, Icit, VTy, Closure)
viewPi = \case
  VPiObj x q i _ a b -> Just (x, SObj, q, i, a, b)
  VPiMeta x i a b -> Just (x, SMeta, Omega, i, a, b)
  _ -> Nothing
