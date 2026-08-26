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

pArrow = symbol "→" <|> symbol "->"

pBind = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Tm
pAtom =
  withPos
    ( (Var <$> pIdent)
        <|> (U <$ char 'U')
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
  optional (char '0') >>= \case
    Nothing -> pure Omega
    Just _ -> pure Zero

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
  pArrow
  cod <- pTm
  pure $ foldr (\(m, xs, a, i) t -> foldr (\x -> Pi x m i a) t xs) cod dom

pFunOrSpine :: Parser Tm
pFunOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _ -> Pi "_" Omega Expl sp <$> pTm

pLet :: Parser Tm
pLet = do
  pKeyword "let"
  m <- pOptMode
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol ";"
  u <- pTm
  pure $ Let x m (maybe Hole id ann) t u

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
