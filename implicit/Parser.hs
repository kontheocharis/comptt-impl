module Parser (parseString, parseStdin) where

import Common
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import Presyntax
import System.Exit
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Tm -> Parser Tm
withPos p = SrcPos <$> getSourcePos <*> p

lexeme = L.lexeme ws

symbol s = lexeme (C.string s)

char c = lexeme (C.char c)

parens p = char '(' *> p <* char ')'

braces p = char '{' *> p <* char '}'

pArrow :: Parser Stage
pArrow =
  (SObj <$ (symbol "→" <|> symbol "->"))
    <|> (SMeta <$ (symbol "⇒" <|> symbol "=>"))

pBind = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "letm" || x == "λ" || x == "U" || x == "UU"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pUniverse :: Parser Tm
pUniverse =
  try (U SMeta <$ pKeyword "UU") <|> (U SObj <$ pKeyword "U")

pLift :: Parser Tm
pLift = do
  C.char '^'
  q <- (Zero <$ C.char '0') <|> pure Omega
  ws
  Lift q <$> pAtom

pQuote :: Parser Tm
pQuote = Quote <$> (char '<' *> pTm <* char '>')

pSplice :: Parser Tm
pSplice = Splice <$> (char '~' *> pAtom)

pAtom :: Parser Tm
pAtom =
  withPos
    ( (Var <$> pIdent)
        <|> pUniverse
        <|> pLift
        <|> pQuote
        <|> pSplice
        <|> (Hole <$ char '_')
    )
    <|> parens pTm

pArg :: Parser (Either Name Icit, Tm)
pArg =
  (try $ braces $ do x <- pIdent; char '='; t <- pTm; pure (Left x, t))
    <|> ((Right Impl,) <$> (char '{' *> pTm <* char '}'))
    <|> ((Right Expl,) <$> pAtom)

pSpine :: Parser Tm
pSpine = do
  h <- pAtom
  args <- many pArg
  pure $ foldl (\t (i, u) -> App t u i) h args

pLamBinder :: Parser (Name, Either Name Icit)
pLamBinder =
  ((,Right Expl) <$> pBind)
    <|> try ((,Right Impl) <$> braces pBind)
    <|> braces (do x <- pIdent; char '='; y <- pBind; pure (y, Left x))

pLam :: Parser Tm
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTm
  pure $ foldr (uncurry Lam) t xs

pOptMode :: Parser Mode
pOptMode =
  (Zero <$ char '0') <|> (Omega <$ char 'ω') <|> pure Omega

pPiBinder :: Parser (Mode, [Name], Tm, Icit)
pPiBinder =
  braces
    ( (,,,Impl)
        <$> pOptMode
        <*> some pBind
        <*> ((char ':' *> pTm) <|> pure Hole)
    )
    <|> parens
      ( (,,,Expl)
          <$> pOptMode
          <*> some pBind
          <*> (char ':' *> pTm)
      )

pPi :: Parser Tm
pPi = do
  dom <- some pPiBinder
  s <- pArrow
  cod <- pTm
  pure $ foldr (\(m, xs, a, i) t -> foldr (\x -> Pi x m i s a) t xs) cod dom

pFunOrSpine :: Parser Tm
pFunOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just s -> Pi "_" Omega Expl s sp <$> pTm

pLet :: Parser Tm
pLet = do
  s <- (SMeta <$ try (pKeyword "letm")) <|> (SObj <$ pKeyword "let")
  m <- pOptMode
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol ";"
  u <- pTm
  pure $ Let x s m (maybe Hole id ann) t u

pTm :: Parser Tm
pTm = withPos (pLam <|> pLet <|> try pPi <|> pFunOrSpine)

pSrc :: Parser Tm
pSrc = ws *> pTm <* eof

parseString :: String -> IO Tm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Tm, String)
parseStdin = do
  src <- getContents
  t <- parseString src
  pure (t, src)
