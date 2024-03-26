{-# LANGUAGE OverloadedStrings #-}
module Elevator.Parser where

import Control.Applicative            (liftA2, liftA3)
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
import Control.Monad.Combinators.NonEmpty qualified as CMCNE
import Text.Megaparsec.Char           qualified as MPC
import Text.Megaparsec.Char.Lexer     qualified as MPCL
import qualified Data.List.NonEmpty as NE
import Control.Monad.RWS (MonadTrans(lift))

type ElParser = Parsec Void Text

fullFileParse :: (ElModeSpec m) => FilePath -> Text -> Either String (ElProgram m)
fullFileParse p = first errorBundlePretty . parse (MPC.space >> ElProgram <$> many parseTop <* eof) p

fullCommandParse :: (ElModeSpec m) => FilePath -> Text -> Either String (Either (ElTop m) (ElTerm m))
fullCommandParse p = first errorBundlePretty . parse (MPC.space >> (Left <$> parseTop <|> Right <$> parseTerm) <* eof) p

parseTop :: (ElModeSpec m) => ElParser (ElTop m)
parseTop = parseTmDefTop

parseTmDefTop :: (ElModeSpec m) => ElParser (ElTop m)
parseTmDefTop = do
  (x, ps, m) <- try $ do
    x <- parseLowerId
    ps <- many parseLowerId
    m <- parseMode
    symbol ":" $> (x, ps, m)
  ty <- parseType
  symbol "="
  t <- parseTerm
  symbol ";;"
  pure . ElTmDef x m ty $ foldr (`TmLam` Nothing) t ps

parseTyDefTop :: (ElModeSpec m) => ElParser (ElTop m)
parseTyDefTop =
  liftA3
    (liftA2 ElTyDef NE.init NE.last)
    (keyword "type" *> CMCNE.some parseLowerId)
    parseMode
    (symbol "=" *> option [] (optional (symbol "|") *> sepBy1 parseTyDefCons (symbol "|")))

parseTyDefCons :: (ElModeSpec m) => ElParser (ElId, [ElType m])
parseTyDefCons =
  liftA2
    (,)
    parseUpperId
    (keyword "of" *> sepBy parseType (symbol "*"))

parseTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseTerm = undefined
-- parseTerm = do
--   t <- choice
--        [ parseLamTerm
--        , parseMatchTm
--        , parseLoadTerm
--        , parseIteTerm
--        , parseBinOpTerm
--        ]
--   f <- option id $ do
--     symbol ":"
--     flip TmAnn <$> parseTy
--   pure $ f t

-- parseLamTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseLamTerm = do
--   keyword "fun"
--   ps <- many parseParam
--   symbol "->"
--   t <- parseTerm
--   pure $ foldr (uncurry TmLam) t ps
--   where
--     parseParam :: (ElModeSpec m) => ElParser (ElId, Maybe (ElType m))
--     parseParam =
--       between (symbol "(") (symbol ")")
--         (liftA2 (,) parseLowerId (symbol ":" *> (Just <$> parseTy)))
--       <|> (, Nothing) <$> parseLowerId

-- parseMatchTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseMatchTerm = undefined

-- parseloadterm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseLoadTerm = do
--   keyword "let"
--   keyword "return"
--   m <- optional parseMode
--   x <- parseLowerId
--   symbol "="
--   t <- parseTerm
--   keyword "in"
--   TmLetRet m x t <$> parseTerm

-- parseIteTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseIteTerm = do
--   keyword "if"
--   t <- parseTerm
--   keyword "then"
--   t0 <- parseTerm
--   keyword "else"
--   TmIte t t0 <$> parseTm

-- parseBinOpTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseBinOpTerm = CMCE.makeExprParser parseApplikeTerm table
--   where
--     table =
--       [ [ CMCE.InfixL $ symbol "*" $> TmBinOp OpMul
--         , CMCE.InfixL $ symbol "/" $> TmBinOp OpDiv
--         , CMCE.InfixL $ symbol "%" $> TmBinOp OpMod
--         ]
--       , [ CMCE.InfixL $ symbol "+" $> TmBinOp OpAdd
--         , CMCE.InfixL $ symbol "-" $> TmBinOp OpSub
--         ]
--       , [ CMCE.InfixN $ symbol "==" $> TmBinOp OpEq
--         , CMCE.InfixN $ symbol "/=" $> TmBinOp OpNe
--         , CMCE.InfixN $ symbol "<=" $> TmBinOp OpLe
--         , CMCE.InfixN $ symbol "<" $> TmBinOp OpLt
--         , CMCE.InfixN $ symbol ">=" $> TmBinOp OpGe
--         , CMCE.InfixN $ symbol ">" $> TmBinOp OpGt
--         ]
--       ]

-- parseApplikeTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseApplikeTerm = parseApplikeShiftTerm <|> parseApplikeConstTerm <|> parseAppTerm

-- parseApplikeShiftTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseApplikeShiftTerm = do
--   f <- choice
--     [ keyword "lift" >> TmLift <$> optional parseMode
--     , keyword "unlift" >> TmUnlift <$> parseMode
--     , keyword "return" >> TmRet <$> optional parseMode
--     ]
--   f <$> parseAtomicTerm

-- parseApplikeConstTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseApplikeConstTerm = do
--   keyword "succ"
--   TmSucc <$> parseAtomicTerm

-- parseAppTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseAppTerm = foldl1' TmApp <$> some parseAtomicTerm

-- parseAtomicTerm :: (ElModeSpec m) => ElParser (ElTerm m)
-- parseAtomicTerm =
--   choice
--     [ TmNat <$> lexeme MPCL.decimal
--     , keyword "true" $> TmTrue
--     , keyword "false" $> TmFalse
--     , TmVar <$> parseLowerId
--     , parened parseTm
--     ]

parseKind :: (ElModeSpec m) => ElParser (ElKind m)
parseKind =
  liftA2
    (foldr (`KiUp` []))
    parseAtomicKind
    (many (keyword "Up" *> parseMode))

parseAtomicKind :: (ElModeSpec m) => ElParser (ElKind m)
parseAtomicKind =
  choice
    [ keyword "Type" $> KiType <*> parseMode
    , bracketed parseContextualKind <*> parseMode
    , parened parseKind
    ]

parseContextualKind :: (ElModeSpec m) => ElParser (m -> ElKind m)
parseContextualKind = do
  ctx <- parseContext
  keyword "Up"
  (\ki m -> KiUp m ctx ki)<$> parseKind

parseContext :: (ElModeSpec m) => ElParser (ElContext m)
parseContext = undefined

parseType :: (ElModeSpec m) => ElParser (ElType m)
parseType = undefined
-- parseType = parseArrType

-- parseArrType :: (ElModeSpec m) => ElParser (ElType m)
-- parseArrType = foldr1 TyArr <$> sepBy1 parseShiftTy (symbol "->")

-- parseShiftType :: (ElModeSpec m) => ElParser (ElType m)
-- parseShiftType = parseNonAtomicShiftTy <|> parseAtomicTy
--   where
--     parseNonAtomicShiftTy = do
--       shift <- (keyword "Up" $> TyUp) <|> (keyword "Down" $> TyDown)
--       m <- parseMode
--       symbol "=>"
--       n <- parseMode
--       shift m n <$> parseShiftType

-- parseAtomicType :: (ElModeSpec m) => ElParser (ElType m)
-- parseAtomicType =
--   choice
--     [ keyword "Int" $> TyInt
--     , keyword "Bool" $> TyBool
--     , between (symbol "(") (symbol ")") parseType
--     ]

parseMode :: (ElModeSpec m) => ElParser m
parseMode = do
  modeText <- between (symbol "<") (symbol ">") (takeWhile1P (Just "mode") (/= '>'))
  case readModeEither (T.unpack modeText) of
    Right m -> pure m
    Left  e -> fail ("invalid mode: " <> e)

parseLowerId :: ElParser ElId
parseLowerId = elId <$> lowerIdentifier

parseUpperId :: ElParser ElId
parseUpperId = elId <$> upperIdentifier

------------------------------------------------------------
-- lexer-like combinators
------------------------------------------------------------

keywords :: [Text]
keywords =
  [ "Up"
  , "Down"
  , "Int"
  , "Bool"
  , "store"
  , "load"
  , "in"
  , "thunk"
  , "force"
  , "fun"
  , "if"
  , "then"
  , "else"
  , "true"
  , "false"
  , "match"
  , "with"
  , "end"
  , "type"
  , "of"
  ]

parened :: ElParser a -> ElParser a
parened = between (symbol "(") (symbol ")")

bracketed :: ElParser a -> ElParser a
bracketed = between (symbol "[") (symbol "]")

symbol :: Text -> ElParser ()
symbol txt = void (lexeme (MPC.string txt)) <?> ("symbol " <> show txt)

keyword :: Text -> ElParser ()
keyword txt
  | txt `elem` keywords = lexeme (MPC.string txt *> notFollowedBy restIdChar) <?> ("keyword " <> show txt)
  | otherwise           = error $ "Parser bug: unknown keyword " <> show txt

lowerIdentifier :: ElParser Text
lowerIdentifier = identifierOf MPC.lowerChar <?> "identifier starting with a lower-case letter"

upperIdentifier :: ElParser Text
upperIdentifier = identifierOf MPC.upperChar <?> "identifier starting with an upper-case letter"

identifierOf :: ElParser Char -> ElParser Text
identifierOf firstChar = identifierImpl
  where
    identifierImpl :: ElParser Text
    identifierImpl = try . withCondition (`notElem` keywords) ((<> "") . show) $
      lexeme ((T.pack .). (:) <$> firstChar <*> many restIdChar)

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
