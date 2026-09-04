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
  = VFlex MetaVar Phase Spine
  | VRigidObj Lvl Mode ~VTy Spine -- records the original mode the variable was bound in
  | VRigidMeta Lvl ~VTy Spine
  | VLamObj Name Mode Icit ~VTy {-# UNPACK #-} Closure
  | VLamMeta Name Icit ~VTy {-# UNPACK #-} Closure
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

pattern VVarObj :: Lvl -> Mode -> VTy -> Val
pattern VVarObj x m a = VRigidObj x m a []

pattern VVarMeta :: Lvl -> VTy -> Val
pattern VVarMeta x a = VRigidMeta x a []

vVar :: Lvl -> Stage -> Mode -> VTy -> Val
vVar x SObj q a = VVarObj x q a
vVar x SMeta _ a = VVarMeta x a

pattern VMeta :: MetaVar -> Phase -> Val
pattern VMeta m ph = VFlex m ph []

vUnitRep :: VRep
vUnitRep = VRep (RUnit (VPol Pos))

viewPi :: Val -> Maybe (Name, Stage, Mode, Icit, VTy, Closure)
viewPi = \case
  VPiObj x q i _ a b -> Just (x, SObj, q, i, a, b)
  VPiMeta x i a b -> Just (x, SMeta, Omega, i, a, b)
  _ -> Nothing
