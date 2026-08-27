module Presyntax where

import Common

data Tm
  = Var Name -- x
  | Lam Name (Either Name Icit) Tm -- \x. t | \{x}. t | \{x = y}. t
  | App Tm Tm (Either Name Icit) -- t u  | t {u} | t {x = u}
  | UMeta -- U'
  | UObj Tm -- U α
  | Pi Name Mode Icit Stage Tm Tm -- (i x : A) -> B | (i x : A) ->' B
  | Lift Mode Tm -- (^A) | (^0 A)
  | Quote Tm -- <t>
  | Splice Tm -- ~t
  | PolU -- Pol
  | Pol Polarity -- + | -
  | RepU Tm -- Rep θ
  | Rep (RepF Tm Tm) -- (* θ) | ▹ α | α => β
  | Producer Tm -- ▶ A
  | Ret Tm -- return t
  | Let Name Stage Mode Tm Tm Tm -- let i x : A = t; u | letm x : A = t; u
  | SrcPos SourcePos Tm -- source position for error reporting
  | Hole -- _
  deriving (Show)
