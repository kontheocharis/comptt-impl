module Code where

import Common (Ix, Name)

data Code
  = CLam Name Code
  | CApp Code Code
  | CVar Ix
  | CLet Name Code Code
  deriving (Show)
