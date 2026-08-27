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

    mode :: Stage -> Mode -> String
    mode SMeta _ = ""
    mode SObj Omega = ""
    mode SObj Zero = "0 "

    liftSym :: Mode -> String
    liftSym Zero = "^0 "
    liftSym Omega = "^"

    letKw :: Stage -> String
    letKw SObj = "let "
    letKw SMeta = "letm "

    arrow :: Stage -> String
    arrow SObj = " → "
    arrow SMeta = " →' "

    piBind ns x s q Expl a = showParen True ((mode s q ++) . (x ++) . (" : " ++) . go letp ns a)
    piBind ns x s q Impl a = bracket ((mode s q ++) . (x ++) . (" : " ++) . go letp ns a)

    lamBind x Impl = bracket (x ++)
    lamBind x Expl = (x ++)

    goBDS :: Int -> [Name] -> MetaVar -> [BD] -> ShowS
    goBDS p ns m bds = case (ns, bds) of
      ([], []) -> (("?" ++ show m) ++)
      (ns :> n, bds :> Bound _ _) -> par p appp $ goBDS appp ns m bds . (' ' :) . (n ++)
      (ns :> n, bds :> Defined) -> goBDS appp ns m bds
      _ -> error "impossible"

    goLam :: [Name] -> Tm -> ShowS
    goLam ns (LamObj (fresh ns -> x) _ i t) = (' ' :) . lamBind x i . goLam (ns :> x) t
    goLam ns (LamMeta (fresh ns -> x) i t) = (' ' :) . lamBind x i . goLam (ns :> x) t
    goLam ns t = (". " ++) . go letp ns t

    goPi :: Stage -> [Name] -> Tm -> ShowS
    goPi _ ns (PiObj (fresh ns -> x) q i _ a b)
      | x /= "_" = (' ' :) . piBind ns x SObj q i a . goPi SObj (ns :> x) b
    goPi _ ns (PiMeta (fresh ns -> x) i a b)
      | x /= "_" = (' ' :) . piBind ns x SMeta Omega i a . goPi SMeta (ns :> x) b
    goPi s ns b = (arrow s ++) . go pip ns b

    goApp :: Int -> [Name] -> Tm -> Tm -> Icit -> ShowS
    goApp p ns t u Expl = par p appp $ go appp ns t . (' ' :) . go atomp ns u
    goApp p ns t u Impl = par p appp $ go appp ns t . (' ' :) . bracket (go letp ns u)

    go :: Int -> [Name] -> Tm -> ShowS
    go p ns = \case
      Var (Ix x) -> ((ns !! x) ++)
      AppObj t u _ i -> goApp p ns t u i
      AppMeta t u i -> goApp p ns t u i
      LamObj (fresh ns -> x) _ i t -> par p letp $ ("λ " ++) . lamBind x i . goLam (ns :> x) t
      LamMeta (fresh ns -> x) i t -> par p letp $ ("λ' " ++) . lamBind x i . goLam (ns :> x) t
      Producer a -> par p appp $ ("▶ " ++) . go atomp ns a
      Ret t -> par p appp $ ("return " ++) . go atomp ns t
      UObj _ a -> par p appp $ ("U " ++) . go atomp ns a
      UMeta -> ("U'" ++)
      Lift q a -> par p appp $ (liftSym q ++) . go atomp ns a
      Splice _ t -> par p appp $ ("~" ++) . go atomp ns t
      Quote _ t -> ("<" ++) . go letp ns t . (">" ++)
      PiObj "_" Omega Expl _ a b -> par p pip $ go appp ns a . (arrow SObj ++) . go pip (ns :> "_") b
      PiMeta "_" Expl a b -> par p pip $ go appp ns a . (arrow SMeta ++) . go pip (ns :> "_") b
      PiObj (fresh ns -> x) q i _ a b -> par p pip $ piBind ns x SObj q i a . goPi SObj (ns :> x) b
      PiMeta (fresh ns -> x) i a b -> par p pip $ piBind ns x SMeta Omega i a . goPi SMeta (ns :> x) b
      Let (fresh ns -> x) s q a t u ->
        par p letp $
          (letKw s ++)
            . (mode s q ++)
            . (x ++)
            . (" : " ++)
            . go letp ns a
            . ("\n  = " ++)
            . go letp ns t
            . (";\n\n" ++)
            . go letp (ns :> x) u
      Meta m _ -> (("?" ++ show m) ++)
      InsertedMeta m _ bds -> goBDS p ns m bds
      PolU -> ("Pol" ++)
      Pol th -> (show th ++)
      RepU th -> par p appp $ ("Rep " ++) . go atomp ns th
      Rep (RUnit th) -> par p appp $ ("unit " ++) . go atomp ns th
      Rep (RProducer a) -> par p appp $ ("▹ " ++) . go atomp ns a
      Rep (RArrow a b) -> par p pip $ go appp ns a . (" ⇒ " ++) . go pip ns b

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