{-# LANGUAGE OverloadedStrings #-}
module Elevator.Parser where

import Control.Applicative            (liftA3)
import Control.Monad                  (void)
import Control.Monad.Combinators.Expr qualified as CMCE
import Data.Bifunctor                 (Bifunctor (first))
import Data.Functor                   (($>))
import Data.List                      (foldl1')
import Data.Text                      (Text)
import Data.Text                      qualified as T
import Data.Tuple.Extra               (uncurry3)
import Data.Void
import Elevator.ModeSpec
import Elevator.Syntax
import Text.Megaparsec
import Text.Megaparsec.Char           qualified as MPC
import Text.Megaparsec.Char.Lexer     qualified as MPCL

type ElParser = Parsec Void Text

fullParse :: (ElModeSpec m) => FilePath -> Text -> Either String (ElTerm m)
fullParse p = first errorBundlePretty . parse (parseTm <* eof) p

parseTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseTm =
  choice
  [ parseLamTm
  , parseLetRetTm
  , parseIteTm
  , parseBinOpTm
  ]

parseLamTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLamTm = do
  keyword "fun"
  ps <- many parseParam
  symbol "->"
  t <- parseTm
  pure $ foldr (uncurry3 TmLam) t ps
  where
    parseParam :: (ElModeSpec m) => ElParser (ElId, m, ElType m)
    parseParam =
      between (symbol "(") (symbol ")") $
        liftA3 (,,) parseId parseMode (symbol ":" *> parseTy)

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

parseIteTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseIteTm = do
  keyword "if"
  t <- parseTm
  keyword "then"
  t0 <- parseTm
  keyword "else"
  TmIte t t0 <$> parseTm

parseBinOpTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseBinOpTm = CMCE.makeExprParser parseApplikeTm table
  where
    table =
      [ [ CMCE.InfixL $ symbol "*" $> TmBinOp OpMul
        , CMCE.InfixL $ symbol "/" $> TmBinOp OpDiv
        , CMCE.InfixL $ symbol "%" $> TmBinOp OpMod
        ]
      , [ CMCE.InfixL $ symbol "+" $> TmBinOp OpAdd
        , CMCE.InfixL $ symbol "-" $> TmBinOp OpSub
        ]
      , [ CMCE.InfixN $ symbol "==" $> TmBinOp OpEq
        , CMCE.InfixN $ symbol "/=" $> TmBinOp OpNe
        , CMCE.InfixN $ symbol "<=" $> TmBinOp OpLe
        , CMCE.InfixN $ symbol "<" $> TmBinOp OpLt
        , CMCE.InfixN $ symbol ">=" $> TmBinOp OpGe
        , CMCE.InfixN $ symbol ">" $> TmBinOp OpGt
        ]
      ]

parseApplikeTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseApplikeTm = parseApplikeShiftTm <|> parseAppTm

parseApplikeShiftTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseApplikeShiftTm = do
  f <- choice
    [ keyword "lift" $> TmLift
    , keyword "unlift" $> TmUnlift
    , keyword "return" $> TmRet
    ]
  m <- parseMode
  n <- parseMode
  f m n <$> parseAtomicTm

parseAppTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseAppTm = foldl1' TmApp <$> some parseAtomicTm

parseAtomicTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseAtomicTm =
  choice
    [ TmNat <$> lexeme MPCL.decimal
    , keyword "true" $> TmTrue
    , keyword "false" $> TmFalse
    , TmVar <$> parseId
    , between (symbol "(") (symbol ")") parseTm
    ]

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
parseAtomicTy =
  choice
    [ keyword "Nat" $> TyNat
    , keyword "Bool" $> TyBool
    , between (symbol "(") (symbol ")") parseTy
    ]

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

keywords :: [Text]
keywords =
  [ "Up"
  , "Down"
  , "Nat"
  , "Bool"
  , "let"
  , "return"
  , "in"
  , "lift"
  , "unlift"
  , "fun"
  , "if"
  , "then"
  , "else"
  , "true"
  , "false"
  ]

symbol :: Text -> ElParser ()
symbol txt = void (lexeme (MPC.string txt)) <?> ("symbol " <> show txt)

keyword :: Text -> ElParser ()
keyword txt
  | txt `elem` keywords = lexeme (MPC.string txt *> notFollowedBy restIdChar) <?> ("keyword " <> show txt)
  | otherwise           = error $ "Parser bug: unknown keyword " <> show txt

identifier :: ElParser Text
identifier = identifierImpl <?> "identifier"
  where
    identifierImpl :: ElParser Text
    identifierImpl = try . withCondition (`notElem` keywords) ((<> "") . show) $
      lexeme ((T.pack .). (:) <$> firstIdChar <*> many restIdChar)

firstIdChar :: ElParser Char
firstIdChar = MPC.letterChar

restIdChar :: ElParser Char
restIdChar = MPC.alphaNumChar <|> oneOf ("_'" :: String)

lexeme :: ElParser a -> ElParser a
lexeme p = p <* MPC.space

withCondition :: (a -> Bool) -> (a -> String) -> ElParser a -> ElParser a
withCondition cond mkMsg p = do
  o <- getOffset
  r <- p
  if cond r
  then return r
  else region (setErrorOffset o) (fail (mkMsg r))
