{-# LANGUAGE OverloadedStrings #-}
module Elevator.Parser where

import Control.Applicative        (liftA3)
import Control.Monad              (void)
import Control.Monad.Combinators  qualified as CMC
import Data.Bifunctor             (Bifunctor (first))
import Data.Functor               (($>))
import Data.List                  (foldl1')
import Data.Text                  (Text)
import Data.Text                  qualified as T
import Data.Tuple.Extra           (uncurry3)
import Data.Void
import Elevator.ModeSpec
import Elevator.Syntax
import Text.Megaparsec
import Text.Megaparsec.Char       qualified as MPC
import Text.Megaparsec.Char.Lexer qualified as MPCL

type ElParser = Parsec Void Text

fullParse :: (ElModeSpec m) => Text -> Either String (ElTerm m)
fullParse = first errorBundlePretty . parse (parseTm <* eof) ""

parseTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseTm = parseLamTm <|> parseLetRetTm <|> parseLiftTm <|> parseUnliftTm <|> parseReturnTm <|> parseAppTm

parseLamTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLamTm = do
  symbol "\\"
  ps <- many parseParam
  t <- parseTm
  pure $ foldr (uncurry3 TmLam) t ps
  where
    parseParam :: (ElModeSpec m) => ElParser (ElId, m, ElType m)
    parseParam =
      between (symbol "(") (symbol ")") $
        liftA3 (,,) parseId parseMode parseTy

parseLetRetTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLetRetTm = do
  keyword "let"
  keyword "return"
  m <- parseMode
  n <- parseMode
  x <- parseId
  symbol "="
  t <- parseTm
  keyword "in"
  TmLetRet m n x t <$> parseTm

parseApplikeShiftTm :: (ElModeSpec m) => Text -> ElParser (ElTerm m)
parseApplikeShiftTm txt = do
  keyword txt
  m <- parseMode
  n <- parseMode
  TmLift m n <$> parseAtomicTm

parseLiftTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLiftTm = parseApplikeShiftTm "lift"

parseUnliftTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseUnliftTm = parseApplikeShiftTm "unlift"

parseReturnTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseReturnTm = parseApplikeShiftTm "return"

parseAppTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseAppTm = foldl1' TmApp <$> some parseAtomicTm

parseAtomicTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseAtomicTm = (TmNat <$> lexeme MPCL.decimal) <|> (TmVar <$> parseId) <|> CMC.between (symbol "(") (symbol ")") parseTm

parseTy :: (ElModeSpec m) => ElParser (ElType m)
parseTy = parseArrTy

parseArrTy :: (ElModeSpec m) => ElParser (ElType m)
parseArrTy = foldr1 TyArr <$> sepBy1 parseShiftTy (symbol "->")

parseShiftTy :: (ElModeSpec m) => ElParser (ElType m)
parseShiftTy = parseNonAtomicShiftTy <|> parseAtomicTy
  where
    parseNonAtomicShiftTy = do
      shift <- (keyword "Up" $> TyUp) <|> (keyword "Down" $> TyDown)
      m <- parseMode
      n <- parseMode
      shift m n <$> parseShiftTy

parseAtomicTy :: (ElModeSpec m) => ElParser (ElType m)
parseAtomicTy = keyword "Nat" $> TyNat <|> CMC.between (symbol "(") (symbol ")") parseTy

parseMode :: (ElModeSpec m) => ElParser m
parseMode = do
  modeText <- between (symbol "<") (symbol ">") (takeWhile1P (Just "mode") (/= '>'))
  case msreadMay (T.unpack modeText) of
    Just m -> pure m
    _      -> fail "invalid mode text"

parseId :: ElParser ElId
parseId = elId <$> identifier

------------------------------------------------------------
-- lexer-like combinators
------------------------------------------------------------

symbol :: Text -> ElParser ()
symbol txt = void (lexeme (MPC.string txt)) <?> ("symbol " <> show txt)

keyword :: Text -> ElParser ()
keyword txt = lexeme (MPC.string txt *> notFollowedBy restIdChar) <?> ("keyword " <> show txt)

firstIdChar :: ElParser Char
firstIdChar = MPC.letterChar

restIdChar :: ElParser Char
restIdChar = MPC.alphaNumChar <|> oneOf ("_'" :: String)

identifier :: ElParser Text
identifier = lexeme ((T.pack .). (:) <$> firstIdChar <*> many restIdChar) <?> "identifier"

lexeme :: ElParser a -> ElParser a
lexeme p = p <* MPC.space
