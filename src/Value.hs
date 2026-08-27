module Value where

import Common
import Syntax

type Env = [Val]

data Elim
  = EApp Val Stage Mode Icit
  | ESplice Mode
  deriving (Show)

type Spine = [Elim]

data Closure = Closure Env Tm deriving (Show)

type VTy = Val

type VRep = Val

type VPol = Val

data Val
  = VFlex MetaVar Marker Spine
  | VRigid Lvl Mode Spine
  | VLam Name Stage Mode Icit {-# UNPACK #-} Closure
  | VPi Name Stage Mode Icit ~VRep ~VTy {-# UNPACK #-} Closure
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

-- Pattern for variables x0 or xω
pattern VVar :: Lvl -> Mode -> Val
pattern VVar x m = VRigid x m []

pattern VMeta :: MetaVar -> Marker -> Val
pattern VMeta m mrk = VFlex m mrk []

vUnitRep :: VRep
vUnitRep = VRep (RUnit (VPol Pos))
