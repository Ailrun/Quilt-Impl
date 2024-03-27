{-# LANGUAGE OverloadedStrings #-}
module Elevator.Parser where

import Control.Applicative            (liftA2, (<**>))
import Control.Monad                  (void)
import Control.Monad.Combinators.Expr qualified as CMCE
import Data.Bifunctor                 (Bifunctor (first))
import Data.Functor                   (($>))
import Data.List                      (foldl')
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
import Data.List.NonEmpty (NonEmpty(..))

type ElParser = Parsec Void Text

fullFileParse :: (ElModeSpec m) => FilePath -> Text -> Either String (ElProgram m)
fullFileParse p = first errorBundlePretty . parse (between MPC.space eof (ElProgram <$> many parseTop)) p

fullCommandParse :: (ElModeSpec m) => FilePath -> Text -> Either String (Either (ElTop m) (ElTerm m))
fullCommandParse p = first errorBundlePretty . parse (between MPC.space eof (Left <$> parseTop <|> Right <$> parseTerm)) p

parseTop :: (ElModeSpec m) => ElParser (ElTop m)
parseTop = parseTyDefTop <|> parseTmDefTop

parseTmDefTop :: (ElModeSpec m) => ElParser (ElTop m)
parseTmDefTop = do
  (x, ps) <- try $ do
    x <- parseLowerId
    ps <- many parseAtomicPattern
    symbol ":" $> (x, ps)
  ty <- parseType
  symbol "="
  t <- parseTerm
  symbol ";;"
  pure . ElTmDef x ty $ foldr (`TmAmbiLam` Nothing) t ps

parseTyDefTop :: (ElModeSpec m) => ElParser (ElTop m)
parseTyDefTop = do
  keyword "type"
  ids <- CMCNE.some parseLowerId
  let
    ys = NE.init ids
    x = NE.last ids
  m <- parseMode
  symbol "="
  cs <- option [] (optional (symbol "|") *> sepBy1 parseTyDefCons (symbol "|"))
  symbol ";;"
  pure $ ElTyDef ys x m cs

parseTyDefCons :: (ElModeSpec m) => ElParser (ElId, [ElType m])
parseTyDefCons =
  liftA2
    (,)
    parseUpperId
    (option [] (keyword "of" *> sepBy1 parseType (symbol "*")))

parseTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseTerm = do
  choice
    [ parseLamTerm
    , parseMatchTerm
    , parseLetTerm
    , parseLoadTerm
    , parseIteTerm
    , parseBinOpTerm
    ]
  <**> parsePostAnn
  where
    parsePostAnn = option id (symbol ":" $> flip TmAnn <*> parseType)

parseLamTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLamTerm = do
  keyword "fun"
  ps <- many parseParam
  symbol "->"
  t <- parseTerm
  pure $ foldr ($) t ps
  where
    parseParam :: (ElModeSpec m) => ElParser (ElTerm m -> ElTerm m)
    parseParam =
      parened (liftA2 TmAmbiLam parsePattern (optional (symbol ":" *> parseContextEntry)))
      <|> flip TmAmbiLam Nothing <$> parseUnitPattern

parseMatchTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseMatchTerm = do
  keyword "match"
  t <- parseTerm
  keyword "with"
  bs <- option [] (optional (symbol "|") *> sepBy1 parseBranch (symbol "|"))
  keyword "end"
  pure $ TmMatch t bs

parseBranch :: (ElModeSpec m) => ElParser (ElBranch m)
parseBranch =
  liftA2
    (,)
    parsePattern
    (symbol "=>" *> parseTerm)

parsePattern :: (ElModeSpec m) => ElParser (ElPattern m)
parsePattern = liftA2 PatConst parseUpperId parseDataArgPatterns <|> parseAtomicPattern
  where
    parseDataArgPatterns = parened (sepBy1 parsePattern (symbol ",")) <|> pure <$> parseUnitPattern

parseAtomicPattern :: (ElModeSpec m) => ElParser (ElPattern m)
parseAtomicPattern =
  parseUnitPattern
  <|> parened (parsePattern <**> option id (symbol "," $> (PatTuple .) . flip (:) <*> sepBy parsePattern (symbol ",")))

parseUnitPattern :: (ElModeSpec m) => ElParser (ElPattern m)
parseUnitPattern =
  choice
    [ PatInt <$> lexeme MPCL.decimal
    , keyword "True" $> PatTrue
    , keyword "False" $> PatFalse
    , PatVar <$> parseLowerId
    , symbol "_" $> PatWild
    ]

parseLetTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLetTerm = do
  keyword "let"
  x <- parsePattern
  mayTy <- optional (symbol ":" *> parseType)
  symbol "="
  t0 <- parseTerm
  keyword "in"
  t1 <- parseTerm
  keyword "end"
  pure $ TmLet x mayTy t0 t1

parseLoadTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseLoadTerm = do
  keyword "load"
  x <- parseLowerId
  mayTy <- optional (symbol ":" *> parseType)
  symbol "="
  t0 <- parseTerm
  keyword "in"
  t1 <- parseTerm
  keyword "end"
  pure $ TmLoad x mayTy t0 t1

parseIteTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseIteTerm = do
  keyword "if"
  t <- parseTerm
  keyword "then"
  t0 <- parseTerm
  keyword "else"
  TmIte t t0 <$> parseTerm

parseBinOpTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseBinOpTerm = CMCE.makeExprParser parseApplikeTerm table
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

parseApplikeTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseApplikeTerm = parseShiftTerm <|> parseDataTerm <|> parseAppTerm

parseShiftTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseShiftTerm = 
  choice
    [ parseSuspCommon TmSusp parseAtomicTerm parseTerm
    , parseForceCommon TmForce parseAtomicTerm
    , keyword "store" $> TmStore <*> parseAtomicTerm
    ]

parseDataTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseDataTerm = liftA2 TmData parseUpperId parseDataArgTerms
  where
    parseDataArgTerms = parened (sepBy1 parseTerm (symbol ",")) <|> pure <$> parseUnitTerm

parseAppTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseAppTerm = liftA2 (Data.List.foldl' TmAmbiApp) parseAtomicTerm (many parseAtomicAmbi)

parseAtomicTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseAtomicTerm =
  parseUnitTerm
  <|> parened (parseTerm <**> option id (symbol "," $> (TmTuple .) . flip (:) <*> sepBy parseTerm (symbol ",")))

parseUnitTerm :: (ElModeSpec m) => ElParser (ElTerm m)
parseUnitTerm =
  choice
    [ TmInt <$> lexeme MPCL.decimal
    , keyword "True" $> TmTrue
    , keyword "False" $> TmFalse
    , TmVar <$> parseLowerId
    ]

parseAtomicAmbi :: (ElModeSpec m) => ElParser (ElAmbi m)
parseAtomicAmbi =
  choice
    [ try (AmCore <$> parseAtomicAmbiCore)
    , try (AmType <$> parseAtomicType)
    , AmTerm <$> parseAtomicTerm
    ]

parseAmbiCore :: (ElModeSpec m) => ElParser (ElAmbiCore m)
parseAmbiCore =
  choice
    [ parseSuspCommon AmSusp parseAtomicAmbiCore parseAmbiCore
    , parseForceCommon AmForce parseAmbiCore
    , parseAtomicAmbiCore
    ]

parseAtomicAmbiCore :: (ElModeSpec m) => ElParser (ElAmbiCore m)
parseAtomicAmbiCore = AmVar <$> parseLowerId <|> parened parseAmbiCore

parseKind :: (ElModeSpec m) => ElParser (ElKind m)
parseKind = liftA2 (foldr ($)) parseAtomicKind (many (keyword "Up" $> flip KiUp [] <*> parseMode))

parseAtomicKind :: (ElModeSpec m) => ElParser (ElKind m)
parseAtomicKind =
  choice
    [ keyword "Type" $> KiType <*> parseMode
    , parseContextualUpCommon KiUp parseKind
    , parened parseKind
    ]

parseType :: (ElModeSpec m) => ElParser (ElType m)
parseType =
  liftA2
    (foldr1 (.))
    (some (try (parseArgSpec <* symbol "->")))
    parseProdType
  where
    parseArgSpec =
      try (parened (liftA2 TyForall parseLowerId (symbol ":" *> parseKind)))
      <|> TyArr <$> parseProdType

parseProdType :: (ElModeSpec m) => ElParser (ElType m)
parseProdType = do
  neTys <- CMCNE.sepBy1 parseType (symbol "*")
  case neTys of
    ty :| [] -> pure ty
    ty :| tys -> pure $ TyProd (ty:tys)

parseAppLikeType :: (ElModeSpec m) => ElParser (ElType m)
parseAppLikeType =
  parseDelayedType
  <|> parsePostType

parseDelayedType :: (ElModeSpec m) => ElParser (ElType m)
parseDelayedType =
  parseSuspCommon TySusp parseAtomicType parseType
  <|> parseForceCommon TyForce parseAtomicType

-- FIXME: "try parseAtomicType" part should work for type construction
parsePostType :: (ElModeSpec m) => ElParser (ElType m)
parsePostType =
  liftA2 (foldr ($)) (try parseAtomicType) (many parsePostOp)
  <|> liftA2 TyData (option [] (parened (sepBy1 parseType (symbol ",")))) parseLowerId
  where
    parsePostOp =
      choice
      [ keyword "Up" $> flip TyUp [] <*> parseMode
      , keyword "Down" $> TyDown <*> parseMode
      , flip (TyData . pure) <$> parseLowerId
      ]

parseAtomicType :: (ElModeSpec m) => ElParser (ElType m)
parseAtomicType =
  choice
    [ TyVar <$> parseLowerId
    , keyword "Int" $> TyInt <*> parseMode
    , keyword "Bool" $> TyBool <*> parseMode
    , parseContextualUpCommon TyUp parseType
    , parened parseType
    ]

parseContextualUpCommon :: (ElModeSpec m) => (m -> ElContext m -> f m -> f m) -> ElParser (f m) -> ElParser (f m)
parseContextualUpCommon cons p = bracketed parseContextualCommon <*> (keyword "Up" *> parseMode)
  where
    parseContextualCommon = liftA2 (curry (flip (uncurry . cons))) parseContext (symbol "|-" *> p)

parseSuspCommon :: (ElModeSpec m) => (ElContextHat m -> f m -> f m) -> ElParser (f m) -> ElParser (f m) -> ElParser (f m)
parseSuspCommon cons ap p = keyword "susp" *> parseOpenItem
  where
    parseOpenItem = cons [] <$> try ap <|> parened (liftA2 cons parseContextHat (symbol "." *> p))

parseForceCommon :: (ElModeSpec m) => (f m -> ElSubst m -> f m) -> ElParser (f m) -> ElParser (f m)
parseForceCommon cons ap = keyword "force" *> liftA2 cons ap (option [] (symbol "with" *> parseSubst))

parseContext :: (ElModeSpec m) => ElParser (ElContext m)
parseContext =
  symbol "." *> many (symbol "," *> parseContextItem)
  <|> sepBy1 parseContextItem (symbol ",")
  where
    parseContextItem = liftA2 (,) parseLowerId (symbol ":" *> parseContextEntry)

parseContextEntry :: (ElModeSpec m) => ElParser (ElContextEntry m)
parseContextEntry =
  try (EntryOfKi <$> parseKind)
  <|> EntryOfTy <$> parseType

parseContextHat :: ElParser (ElContextHat m)
parseContextHat =
  symbol "." *> many (symbol "," *> parseLowerId)
  <|> sepBy1 parseLowerId (symbol ",")

parseSubst :: (ElModeSpec m) => ElParser (ElSubst m)
parseSubst = parened (sepBy parseTerm (symbol ","))

parseMode :: (ElModeSpec m) => ElParser m
parseMode = do
  modeText <- angled (takeWhile1P (Just "mode") (/= '>'))
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
  [ "Type"
  , "Up"
  , "Down"
  , "Int"
  , "Bool"
  , "store"
  , "load"
  , "in"
  , "susp"
  , "force"
  , "let"
  , "fun"
  , "if"
  , "then"
  , "else"
  , "True"
  , "False"
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

angled :: ElParser a -> ElParser a
angled = between (symbol "<") (symbol ">")

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
