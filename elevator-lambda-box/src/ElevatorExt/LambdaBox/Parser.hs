{-# LANGUAGE OverloadedStrings #-}
module ElevatorExt.LambdaBox.Parser where

import           Control.Applicative            (liftA2)
import           Control.Monad                  (void)
import qualified Control.Monad.Combinators.Expr as CMCE
import           Data.Bifunctor                 (Bifunctor (first))
import           Data.Functor                   (($>))
import           Data.List                      (foldl1')
import           Data.Text                      (Text)
import qualified Data.Text                      as T
import           Data.Void
import           Elevator.Syntax                (ElBinOp (..), ElId, elId)
import           ElevatorExt.LambdaBox.Syntax
import           Text.Megaparsec
import qualified Text.Megaparsec.Char           as MPC
import qualified Text.Megaparsec.Char.Lexer     as MPCL

type ElxParser = Parsec Void Text

fullFileParse :: FilePath -> Text -> Either String ElxProgram
fullFileParse p = first errorBundlePretty . parse (MPC.space >> ElxProgram <$> many parseTopx <* eof) p

fullCommandParse :: FilePath -> Text -> Either String (Either ElxTop ElxTerm)
fullCommandParse p = first errorBundlePretty . parse (MPC.space >> (Left <$> parseTopx <|> Right <$> parseTmx) <* eof) p

parseTopx :: ElxParser ElxTop
parseTopx = do
  (x, ps) <- try $ do
    x <- parseId
    ps <- fmap (, Nothing) <$> many parseId
    symbol ":"
    pure (x, ps)
  ty <- parseTyx
  symbol "="
  t <- parseTmx
  symbol ";;"
  pure $ ElxDef x ty (foldr (uncurry TmxLam) t ps)

parseTmx :: ElxParser ElxTerm
parseTmx = do
  t <- choice
       [ parseLamTmx
       , parseNatCaseTmx
       , parseLetBoxTmx
       , parseIteTmx
       , parseBinOpTmx
       ]
  f <- option id $ do
    symbol ":"
    flip TmxAnn <$> parseTyx
  pure $ f t

parseLamTmx :: ElxParser ElxTerm
parseLamTmx = do
  keyword "fun"
  ps <- many parseParam
  symbol "->"
  t <- parseTmx
  pure $ foldr (uncurry TmxLam) t ps
  where
    parseParam :: ElxParser (ElId, Maybe ElxType)
    parseParam =
      between (symbol "(") (symbol ")")
        (liftA2 (,) parseId (symbol ":" *> (Just <$> parseTyx)))
      <|> (, Nothing) <$> parseId

parseNatCaseTmx :: ElxParser ElxTerm
parseNatCaseTmx = do
  keyword "case"
  t <- parseTmx
  keyword "of"
  symbol "|"
  symbol "0"
  symbol "->"
  tz <- parseTmx
  symbol "|"
  keyword "succ"
  x <- parseId
  symbol "->"
  ts <- parseTmx
  keyword "end"
  pure $ TmxNatCase t tz x ts

parseLetBoxTmx :: ElxParser ElxTerm
parseLetBoxTmx = do
  keyword "let"
  keyword "box"
  x <- parseId
  symbol "="
  t <- parseTmx
  keyword "in"
  TmxLetBox x t <$> parseTmx

parseIteTmx :: ElxParser ElxTerm
parseIteTmx = do
  keyword "if"
  t <- parseTmx
  keyword "then"
  t0 <- parseTmx
  keyword "else"
  TmxIte t t0 <$> parseTmx

parseBinOpTmx :: ElxParser ElxTerm
parseBinOpTmx = CMCE.makeExprParser parseApplikeTmx table
  where
    table =
      [ [ CMCE.InfixL $ symbol "*" $> TmxBinOp OpMul
        , CMCE.InfixL $ symbol "/" $> TmxBinOp OpDiv
        , CMCE.InfixL $ symbol "%" $> TmxBinOp OpMod
        ]
      , [ CMCE.InfixL $ symbol "+" $> TmxBinOp OpAdd
        , CMCE.InfixL $ symbol "-" $> TmxBinOp OpSub
        ]
      , [ CMCE.InfixN $ symbol "==" $> TmxBinOp OpEq
        , CMCE.InfixN $ symbol "/=" $> TmxBinOp OpNe
        , CMCE.InfixN $ symbol "<=" $> TmxBinOp OpLe
        , CMCE.InfixN $ symbol "<" $> TmxBinOp OpLt
        , CMCE.InfixN $ symbol ">=" $> TmxBinOp OpGe
        , CMCE.InfixN $ symbol ">" $> TmxBinOp OpGt
        ]
      ]

parseApplikeTmx :: ElxParser ElxTerm
parseApplikeTmx = parseApplikeBoxTmx <|> parseApplikeConstTmx <|> parseAppTmx

parseApplikeBoxTmx :: ElxParser ElxTerm
parseApplikeBoxTmx = do
  keyword "box"
  TmxBox <$> parseAtomicTmx

parseApplikeConstTmx :: ElxParser ElxTerm
parseApplikeConstTmx = do
  keyword "succ"
  TmxSucc <$> parseAtomicTmx

parseAppTmx :: ElxParser ElxTerm
parseAppTmx = foldl1' TmxApp <$> some parseAtomicTmx

parseAtomicTmx :: ElxParser ElxTerm
parseAtomicTmx =
  choice
    [ TmxNat <$> lexeme MPCL.decimal
    , keyword "true" $> TmxTrue
    , keyword "false" $> TmxFalse
    , TmxVar <$> parseId
    , between (symbol "(") (symbol ")") parseTmx
    ]

parseTyx :: ElxParser ElxType
parseTyx = parseArrTyx

parseArrTyx :: ElxParser ElxType
parseArrTyx = foldr1 TyxArr <$> sepBy1 parseBoxTyx (symbol "->")

parseBoxTyx :: ElxParser ElxType
parseBoxTyx = parseNonAtomicBoxTyx <|> parseAtomicTyx
  where
    parseNonAtomicBoxTyx = do
      keyword "Box"
      TyxBox <$> parseBoxTyx

parseAtomicTyx :: ElxParser ElxType
parseAtomicTyx =
  choice
    [ keyword "Nat" $> TyxNat
    , keyword "Bool" $> TyxBool
    , between (symbol "(") (symbol ")") parseTyx
    ]

parseId :: ElxParser ElId
parseId = elId <$> identifier

------------------------------------------------------------
-- lexer-like combinators
------------------------------------------------------------

keywords :: [Text]
keywords =
  [ "Box"
  , "Nat"
  , "Bool"
  , "let"
  , "box"
  , "in"
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

symbol :: Text -> ElxParser ()
symbol txt = void (lexeme (MPC.string txt)) <?> ("symbol " <> show txt)

keyword :: Text -> ElxParser ()
keyword txt
  | txt `elem` keywords = lexeme (MPC.string txt *> notFollowedBy restIdChar) <?> ("keyword " <> show txt)
  | otherwise           = error $ "Parser bug: unknown keyword " <> show txt

identifier :: ElxParser Text
identifier = identifierImpl <?> "identifier"
  where
    identifierImpl :: ElxParser Text
    identifierImpl = try . withCondition (`notElem` keywords) ((<> "") . show) $
      lexeme ((T.pack .). (:) <$> firstIdChar <*> many restIdChar)

firstIdChar :: ElxParser Char
firstIdChar = MPC.letterChar

restIdChar :: ElxParser Char
restIdChar = MPC.alphaNumChar <|> oneOf ("_'" :: String)

lexeme :: ElxParser a -> ElxParser a
lexeme p = p <* MPC.space

withCondition :: (a -> Bool) -> (a -> String) -> ElxParser a -> ElxParser a
withCondition cond mkMsg p = do
  o <- getOffset
  r <- p
  if cond r
  then return r
  else region (setErrorOffset o) (fail (mkMsg r))
