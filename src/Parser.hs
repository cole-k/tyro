module Parser where

import Lang

import Data.Bifunctor
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Map as M
import qualified Text.Megaparsec.Char.Lexer as L

-- !!! The syntax for this language is pretty simple and subject to change !!!
-- It should be warning enough that this is a toy language, but don't expect its
-- syntax to stay the same between commits.

-- A good chunk of this is written with help from this nice Megaparsec tutorial
-- https://markkarpov.com/megaparsec/parsing-simple-imperative-language.html
type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 lineComment blockComment
  where
    -- Just use Haskell's for now, even if they aren't super great (I'm looking
    -- at you, block comments)
    lineComment  = L.skipLineComment "--"
    blockComment = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

identifier :: Parser String
identifier = lexeme $ (:) <$> letterChar <*> many alphaNumChar

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

var :: Parser TermU
var = try $ do
  name <- identifier
  pure $ varU name

unit :: Parser TermU
unit = try $ do
  symbol "()" *> pure unitU

lambda :: Parser TermU
lambda = try $ do
  _ <- symbol "\\"
  xs <- some identifier
  _ <- symbol "->"
  e <- term
  pure $ multiLamU xs e

record :: Parser TermU
record = try $ do
  row <- braces $ rowAtom `sepBy` rowSeparator
  pure $ rcdU (M.fromList row)
  where
    rowAtom = do
      lbl <- identifier
      _ <- symbol ":"
      e <- term
      pure (lbl, e)
    rowSeparator = symbol ","

projection :: Parser TermU
projection = try $ do
  tm <- term'
  _ <- symbol "."
  lbl <- identifier
  pure $ prjU tm lbl

app :: Parser TermU
app = try $ do
  e1 <- term'
  e2 <- term
  pure $ appU e1 e2

term' :: Parser TermU
term' = choice
  [ var
  , unit
  , lambda
  , record
  , parens term]

term :: Parser TermU
term = app <|> projection <|> term'

parseTerm :: String -> Either String TermU
parseTerm = first (errorBundlePretty) . runParser term ""
