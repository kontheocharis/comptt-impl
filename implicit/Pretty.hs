module Pretty (prettyTm, showTm0, showCode0, displayMetas) where

import Code (Code (..))
import Common
import Control.Monad
import Data.IORef
import qualified Data.IntMap.Strict as IM
import {-# SOURCE #-} Evaluation
import Metacontext
import Syntax
import Text.Printf

--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x
  | elem x ns = fresh ns (x ++ "'")
  | otherwise = x

-- printing precedences
atomp = 4 :: Int -- U, var

appp = 3 :: Int -- application

pip = 1 :: Int -- pi

letp = 0 :: Int -- let, lambda

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec
  where
    bracket :: ShowS -> ShowS
    bracket ss = ('{' :) . ss . ('}' :)

    mode :: Mode -> String
    mode q = (show q ++ " ")

    arrow :: Stage -> String
    arrow SObj = " → "
    arrow SMeta = " →^ "

    piBind ns x q Expl a = showParen True ((mode q ++) . (x ++) . (" : " ++) . go letp ns a)
    piBind ns x q Impl a = bracket ((mode q ++) . (x ++) . (" : " ++) . go letp ns a)

    lamBind x Impl = bracket (x ++)
    lamBind x Expl = (x ++)

    goBDS :: Int -> [Name] -> MetaVar -> [BD] -> ShowS
    goBDS p ns m bds = case (ns, bds) of
      ([], []) -> (("?" ++ show m) ++)
      (ns :> n, bds :> Bound _ _) -> par p appp $ goBDS appp ns m bds . (' ' :) . (n ++)
      (ns :> n, bds :> Defined) -> goBDS appp ns m bds
      _ -> error "impossible"

    go :: Int -> [Name] -> Tm -> ShowS
    go p ns = \case
      Var (Ix x) _ -> ((ns !! x) ++)
      App t u _ _ Expl -> par p appp $ go appp ns t . (' ' :) . go atomp ns u
      App t u _ _ Impl -> par p appp $ go appp ns t . (' ' :) . bracket (go letp ns u)
      Lam (fresh ns -> x) _ q i t -> par p letp $ ("λ " ++) . lamBind x i . goLam (ns :> x) t
        where
          goLam ns (Lam (fresh ns -> x) _ q i t) =
            (' ' :) . lamBind x i . goLam (ns :> x) t
          goLam ns t =
            (". " ++) . go letp ns t
      U SObj -> ("U" ++)
      U SMeta -> ("U^" ++)
      Lift a -> par p appp $ ("^" ++) . go atomp ns a
      Splice t -> par p appp $ ("~" ++) . go atomp ns t
      Quote t -> ("<" ++) . go letp ns t . (">" ++)
      Pi "_" s Omega Expl a b -> par p pip $ go appp ns a . (arrow s ++) . go pip (ns :> "_") b
      Pi (fresh ns -> x) s q i a b -> par p pip $ piBind ns x q i a . goPi s (ns :> x) b
        where
          goPi _ ns (Pi (fresh ns -> x) s' q i a b)
            | x /= "_" = piBind ns x q i a . goPi s' (ns :> x) b
          goPi s ns b = (arrow s ++) . go pip ns b
      Let (fresh ns -> x) _ q a t u ->
        par p letp $
          ("let " ++)
            . (mode q ++)
            . (x ++)
            . (" : " ++)
            . go letp ns a
            . ("\n  = " ++)
            . go letp ns t
            . (";\n\n" ++)
            . go letp (ns :> x) u
      Meta m _ -> (("?" ++ show m) ++)
      InsertedMeta m _ bds -> goBDS p ns m bds

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved mrk -> printf "let ?%s = %s?;\n" (show m) (printMarker mrk)
    Solved mrk v -> printf "let ?%s = %s%s;\n" (show m) (printMarker mrk) (showTm0 $ quote 0 v)
  putStrLn ""
  where
    printMarker :: Marker -> String
    printMarker Absent = ""
    printMarker Present = "λ{#}. "

prettyCode :: Int -> [Name] -> Code -> ShowS
prettyCode prec = go prec
  where
    go :: Int -> [Name] -> Code -> ShowS
    go p ns = \case
      CVar (Ix x) -> ((ns !! x) ++)
      CApp t u -> par p appp $ go appp ns t . (' ' :) . go atomp ns u
      CLam (fresh ns -> x) t -> par p letp $ ("λ " ++) . (x ++) . goLam (ns :> x) t
        where
          goLam ns (CLam (fresh ns -> x) t) =
            (' ' :) . (x ++) . goLam (ns :> x) t
          goLam ns t =
            (". " ++) . go letp ns t
      CLet (fresh ns -> x) t u ->
        par p letp $
          ("let " ++)
            . (x ++)
            . (" = " ++)
            . go letp ns t
            . (";\n\n" ++)
            . go letp (ns :> x) u

showCode0 :: Code -> String
showCode0 t = prettyCode 0 [] t []