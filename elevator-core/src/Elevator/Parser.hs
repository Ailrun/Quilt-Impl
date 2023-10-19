{-# LANGUAGE OverloadedStrings #-}
module Elevator.Parser where

import Control.Applicative            (liftA2)
import Control.Monad                  (void)
import Control.Monad.Combinators.Expr qualified as CMCE
import Data.Bifunctor                 (Bifunctor (first))
import Data.Functor                   (($>))
import Data.List                      (foldl1')
import Data.Text                      (Text)
import Data.Text                      qualified as T
import Data.Void
import Elevator.ModeSpec
import Elevator.Syntax
import Text.Megaparsec
import Text.Megaparsec.Char           qualified as MPC
import Text.Megaparsec.Char.Lexer     qualified as MPCL

type ElParser = Parsec Void Text

fullFileParse :: (ElModeSpec m) => FilePath -> Text -> Either String (ElProgram m)
fullFileParse p = first errorBundlePretty . parse (MPC.space >> ElProgram <$> many parseTop <* eof) p

fullCommandParse :: (ElModeSpec m) => FilePath -> Text -> Either String (Either (ElTop m) (ElTerm m))
fullCommandParse p = first errorBundlePretty . parse (MPC.space >> (Left <$> parseTop <|> Right <$> parseTm) <* eof) p

parseTop :: (ElModeSpec m) => ElParser (ElTop m)
parseTop = do
  (x, ps) <- try $ do
    x <- parseId
    ps <- fmap (, Nothing) <$> many parseId
    symbol ":"
    pure (x, ps)
  m <- parseMode
  ty <- parseTy
  symbol "="
  t <- parseTm
  symbol ";;"
  pure $ ElDef x m ty (foldr (uncurry TmLam) t ps)

parseTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseTm = do
  t <- choice
       [ parseLamTm
       , parseNatCaseTm
       , parseLetRetTm
       , parseIteTm
       , parseBinOpTm
       ]
  f <- option id $ do
    symbol ":"
    flip TmAnn <$> parseTy
  pure $ f t

parseLamTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLamTm = do
  keyword "fun"
  ps <- many parseParam
  symbol "->"
  t <- parseTm
  pure $ foldr (uncurry TmLam) t ps
  where
    parseParam :: (ElModeSpec m) => ElParser (ElId, Maybe (ElType m))
    parseParam =
      between (symbol "(") (symbol ")")
        (liftA2 (,) parseId (symbol ":" *> (Just <$> parseTy)))
      <|> (, Nothing) <$> parseId

parseNatCaseTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseNatCaseTm = do
  keyword "case"
  t <- parseTm
  keyword "of"
  symbol "|"
  symbol "0"
  symbol "->"
  tz <- parseTm
  symbol "|"
  keyword "succ"
  x <- parseId
  symbol "->"
  ts <- parseTm
  keyword "end"
  pure $ TmNatCase t tz x ts

parseLetRetTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLetRetTm = do
  keyword "let"
  keyword "return"
  m <- optional parseMode
  x <- parseId
  symbol "="
  t <- parseTm
  keyword "in"
  TmLetRet m x t <$> parseTm

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
parseApplikeTm = parseApplikeShiftTm <|> parseApplikeConstTm <|> parseAppTm

parseApplikeShiftTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseApplikeShiftTm = do
  f <- choice
    [ keyword "lift" >> TmLift <$> optional parseMode
    , keyword "unlift" >> TmUnlift <$> parseMode
    , keyword "return" >> TmRet <$> optional parseMode
    ]
  f <$> parseAtomicTm

parseApplikeConstTm :: (ElModeSpec m) => ElParser (ElTerm m)
parseApplikeConstTm = do
  keyword "succ"
  TmSucc <$> parseAtomicTm

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
      symbol "=>"
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
  case readModeEither (T.unpack modeText) of
    Right m -> pure m
    Left  e -> fail ("invalid mode: " <> e)

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
  , "case"
  , "of"
  , "succ"
  , "end"
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
