{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}
module Quilt.Parser where

#if MIN_VERSION_base(4,18,0)
import Control.Applicative                ((<**>))
#else
import Control.Applicative                (liftA2, (<**>))
#endif
import Control.Monad                      (void)
import Control.Monad.Combinators.Expr     qualified as CMCE
import Control.Monad.Combinators.NonEmpty qualified as CMCNE
import Data.Bifunctor                     (Bifunctor (first))
import Data.Functor                       (($>))
import Data.List                          (foldl')
import Data.List.NonEmpty                 (NonEmpty (..))
import Data.List.NonEmpty                 qualified as NE
import Data.Sequence                      (Seq (Empty))
import Data.Sequence                      qualified as Seq
import Data.Text                          (Text)
import Data.Text                          qualified as T
import Data.Void                          (Void)
import Text.Megaparsec
import Text.Megaparsec.Char               qualified as MPC
import Text.Megaparsec.Char.Lexer         qualified as MPCL

import Quilt.ModeSpec
import Quilt.Syntax

type QParser = Parsec Void Text

readEitherCompleteFile :: (QModeSpec m) => FilePath -> Text -> Either String (QModule m)
readEitherCompleteFile = runCompleteParser parseModule

readEitherCompleteCommand :: (QModeSpec m) => FilePath -> Text -> Either String (QCommand m)
readEitherCompleteCommand = runCompleteParser parseCommand

runCompleteParser :: QParser a -> FilePath -> Text -> Either String a
runCompleteParser p fp = first errorBundlePretty . parse (between space eof p) fp

parseCommand :: (QModeSpec m) => QParser (QCommand m)
parseCommand = ComTop <$> try parseTop <|> ComTerm <$> parseTerm

parseModule :: (QModeSpec m) => QParser (QModule m)
parseModule = liftA2 QModule (many parseImport) (many parseTop)

parseImport :: QParser QModuleId
parseImport = do
  keyword "require"
  modId <- parseModuleId
  toplevelDelimiter
  pure modId

parseModuleId :: QParser QModuleId
parseModuleId = QModuleId <$> sepBy1 parseUpperId (symbol "/")

parseTop :: (QModeSpec m) => QParser (QTop m)
parseTop = parseTyDefTop <|> parseTmDefTop

parseTyDefTop :: (QModeSpec m) => QParser (QTop m)
parseTyDefTop = impl <?> "top-level type definition"
  where
    impl = do
      keyword "data"
      args <- parseTyDefArgs
      x <- parseUpperId
      m <- parseMode
      cs <- option [] $ do
        symbol "="
        sepStartBy1 parseTyDefCons (symbol "|" <?> "more constructors separated by \"|\"")
      toplevelDelimiter
      pure $ TopTypeDef args x m cs

    parseTyDefArgs =
      parened (sepBy parseTyDefArg (symbol "*" <?> "more type constructor arguments separated by \"*\""))
      <|> option [] (pure . (, Nothing) <$> parseLowerId)

    parseTyDefArg =
      parseOptAnn
        (, Nothing)
        (\x -> (x,) . Just)
        parseLowerId
        (symbol ":" *> parseKind)

parseTmDefTop :: (QModeSpec m) => QParser (QTop m)
parseTmDefTop = do
  x <- parseLowerId <?> "identifier for term definition"
  ps <- many parseAtomicPattern
  symbol ":"
  ty <- parseType
  symbol "="
  t <- parseTerm <?> "term definition"
  toplevelDelimiter
  pure . TopTermDef x ty $ foldr (`TmAmbiLam` Nothing) t ps

parseTyDefCons :: (QModeSpec m) => QParser (QId, [QType m])
parseTyDefCons =
  liftA2
    (,)
    parseUpperId
    (option [] (keyword "of" *> sepBy1 parseAppLikeType (symbol "*" <?> "more term constructor argument types separated by \"*\"")))
  <?> "type constructor definition"

parseTerm :: (QModeSpec m) => QParser (QTerm m)
parseTerm = parseOptAnn id TmAnn impl (symbol ":" *> parseType <?> "type annotation") <?> "term"
  where
    impl =
      choice
        [ parseLamTerm
        , parseMatchTerm
        , parseLetTerm
        , parseLoadTerm
        , parseIteTerm
        , parseBinOpTerm
        ]

parseLamTerm :: (QModeSpec m) => QParser (QTerm m)
parseLamTerm = do
  keyword "fun"
  ps <- some parseParam
  symbol "->" <|> symbol "-o"
  t <- parseTerm
  pure $ foldr ($) t ps
  where
    parseParam :: (QModeSpec m) => QParser (QTerm m -> QTerm m)
    parseParam =
      parened (liftA2 TmAmbiLam parsePattern (optional (symbol ":" *> parseContextEntry)))
      <|> flip TmAmbiLam Nothing <$> parseAtomicPattern

parseMatchTerm :: (QModeSpec m) => QParser (QTerm m)
parseMatchTerm = do
  keyword "match"
  t <- parseTerm
  mayTy <- optional (symbol ":" *> parseType)
  keyword "with"
  bs <- sepStartBy parseBranch (symbol "|" <?> "one more branch separated by \"|\"")
  keyword "end"
  pure $ TmMatch t mayTy bs

parseBranch :: (QModeSpec m) => QParser (QBranch m)
parseBranch =
  liftA2
    (,)
    parsePattern
    (symbol "=>" *> parseTerm)

parsePattern :: (QModeSpec m) => QParser (QPattern m)
parsePattern =
  choice
    [ keyword "load" $> PatLoad <*> parseAtomicPattern
    , try $ liftA2 PatData parseUpperId parseDataArgPatterns
    , parseAtomicPattern
    ]
  <?> "pattern"
  where
    parseDataArgPatterns =
      pure <$> parseUnitPattern
      <|> NE.toList <$> parseTupleLikePattern

parseAtomicPattern :: (QModeSpec m) => QParser (QPattern m)
parseAtomicPattern =
  parseUnitPattern
  <|> wrapTupleLike <$> parseTupleLikePattern
  where
    wrapTupleLike (pat :| []) = pat
    wrapTupleLike pats        = PatTuple (NE.toList pats)

parseTupleLikePattern :: (QModeSpec m) => QParser (NonEmpty (QPattern m))
parseTupleLikePattern = parened (CMCNE.sepBy1 parsePattern (symbol ","))

parseUnitPattern :: (QModeSpec m) => QParser (QPattern m)
parseUnitPattern =
  choice
    [ PatInt <$> lexeme MPCL.decimal
    , keyword "True" $> PatTrue
    , keyword "False" $> PatFalse
    , PatVar <$> parseLowerId
    , flip PatData [] <$> parseUpperId
    , symbol "_" $> PatWild
    ]

parseLetTerm :: (QModeSpec m) => QParser (QTerm m)
parseLetTerm = do
  keyword "let"
  pat <- parsePattern
  mayTy <- optional (symbol ":" *> parseType)
  symbol "="
  t0 <- parseTerm
  keyword "in"
  t1 <- parseTerm
  pure $ TmMatch t0 mayTy [(pat, t1)]

parseLoadTerm :: (QModeSpec m) => QParser (QTerm m)
parseLoadTerm = do
  keyword "load"
  pat <- parsePattern
  mayTy <- optional (symbol ":" *> parseType)
  symbol "="
  t0 <- parseTerm
  keyword "in"
  t1 <- parseTerm
  pure $ TmMatch t0 mayTy [(PatLoad pat, t1)]

parseIteTerm :: (QModeSpec m) => QParser (QTerm m)
parseIteTerm = do
  keyword "if"
  t <- parseTerm
  keyword "then"
  t0 <- parseTerm
  keyword "else"
  TmIte t t0 <$> parseTerm

parseBinOpTerm :: (QModeSpec m) => QParser (QTerm m)
parseBinOpTerm = CMCE.makeExprParser parseApplikeTerm table
  where
    table =
      [ [ CMCE.InfixL (symbol "*" $> TmBinOp OpMul <?> "operator \"*\"")
        , CMCE.InfixL (symbol "/" $> TmBinOp OpDiv <?> "operator \"/\"")
        , CMCE.InfixL (symbol "%" $> TmBinOp OpMod <?> "operator \"%\"")
        ]
      , [ CMCE.InfixL (symbol "+" $> TmBinOp OpAdd <?> "operator \"+\"")
        , CMCE.InfixL (symbol "-" $> TmBinOp OpSub <?> "operator \"-\"")
        ]
      , [ CMCE.InfixN (symbol "==" $> TmBinOp OpEq <?> "operator \"==\"")
        , CMCE.InfixN (symbol "/=" $> TmBinOp OpNe <?> "operator \"/=\"")
        , CMCE.InfixN (symbol "<=" $> TmBinOp OpLe <?> "operator \"<=\"")
        , CMCE.InfixN (symbol "<" $> TmBinOp OpLt <?> "operator \"<\"")
        , CMCE.InfixN (symbol ">=" $> TmBinOp OpGe <?> "operator \">=\"")
        , CMCE.InfixN (symbol ">" $> TmBinOp OpGt <?> "operator \">\"")
        ]
      ]

parseApplikeTerm :: (QModeSpec m) => QParser (QTerm m)
parseApplikeTerm = parseShiftTerm <|> try parseDataTerm <|> parseAppTerm

parseShiftTerm :: (QModeSpec m) => QParser (QTerm m)
parseShiftTerm =
  choice
    [ parseSuspCommon TmSusp parseAtomicTerm parseTerm
    , parseForceCommon TmForce parseAtomicTerm
    , keyword "alloc" $> TmStore <*> parseAtomicTerm
    ]

parseDataTerm :: (QModeSpec m) => QParser (QTerm m)
parseDataTerm = liftA2 TmData parseUpperId parseDataArgTerms
  where
    parseDataArgTerms =
      pure <$> parseUnitTerm
      <|> NE.toList <$> parseTupleLikeTerm

parseAppTerm :: (QModeSpec m) => QParser (QTerm m)
parseAppTerm = liftA2 (Data.List.foldl' TmAmbiApp) parseAtomicTerm (many parseAtomicAmbi)

parseAtomicTerm :: (QModeSpec m) => QParser (QTerm m)
parseAtomicTerm =
  parseUnitTerm
  <|> wrapTupleLike <$> parseTupleLikeTerm
  <?> "term"
  where
    wrapTupleLike (t :| []) = t
    wrapTupleLike ts        = TmTuple (NE.toList ts)

parseTupleLikeTerm :: (QModeSpec m) => QParser (NonEmpty (QTerm m))
parseTupleLikeTerm = parened (CMCNE.sepBy1 parseTerm (symbol ","))

parseUnitTerm :: (QModeSpec m) => QParser (QTerm m)
parseUnitTerm =
  choice
    [ TmInt <$> lexeme MPCL.decimal
    , keyword "True" $> TmTrue
    , keyword "False" $> TmFalse
    , build <$> parseLowerId
    , flip TmData [] <$> parseUpperId
    ]
  where
    build x
      | Just bi <- toBuiltIn x = TmBuiltIn bi
      | otherwise              = TmVar x

parseAmbi :: (QModeSpec m) => QParser (QAmbi m)
parseAmbi =
  choice
    [ try (AmCore <$> hidden parseAmbiCore)
    , try (AmType <$> parseType)
    , AmTerm <$> parseTerm
    ]

parseAtomicAmbi :: (QModeSpec m) => QParser (QAmbi m)
parseAtomicAmbi =
  choice
    [ try (AmCore <$> hidden parseAtomicAmbiCore)
    , try (AmType <$> parseAtomicType)
    , AmTerm <$> parseAtomicTerm
    ]

parseAmbiCore :: (QModeSpec m) => QParser (QAmbiCore m)
parseAmbiCore =
  choice
    [ parseSuspCommon AmSusp parseAtomicAmbiCore parseAmbiCore
    , parseForceCommon AmForce parseAmbiCore
    , parseAtomicAmbiCore
    ]

parseAtomicAmbiCore :: (QModeSpec m) => QParser (QAmbiCore m)
parseAtomicAmbiCore = AmVar <$> parseLowerId <|> parened parseAmbiCore

parseKind :: (QModeSpec m) => QParser (QKind m)
parseKind = liftA2 (foldr ($)) parseAtomicKind (many (keyword "Up" $> flip KiUp Seq.empty <*> parseMode)) <?> "kind"

parseAtomicKind :: (QModeSpec m) => QParser (QKind m)
parseAtomicKind =
  choice
    [ keyword "Type" $> KiType <*> parseMode <?> "kind \"Type\""
    , parseContextualUpCommon KiUp parseKind
    , parened parseKind
    ]
  <?> "kind"

parseType :: (QModeSpec m) => QParser (QType m)
parseType =
  parseOptAnn
    id
    TyAnn
    (liftA2
     (flip (foldr ($)))
     (many (try (parseArgSpec <* (symbol "->" <|> symbol "-o"))))
     parseProdType)
    (symbol ":" *> parseKind <?> "kind annotation")
  <?> "type"
  where
    parseArgSpec =
      try (parened (liftA2 TyForall parseLowerId (symbol ":" *> parseKind)))
      <|> TyArr <$> parseProdType
      <?> "argument type"

parseProdType :: (QModeSpec m) => QParser (QType m)
parseProdType = do
  neTys <- CMCNE.sepBy1 parseAppLikeType (symbol "*" <?> "one more product type item separated by \"*\"")
  case neTys of
    ty :| []  -> pure ty
    ty :| tys -> pure $ TyProd (ty:tys)

parseAppLikeType :: (QModeSpec m) => QParser (QType m)
parseAppLikeType =
  parseDelayedType
  <|> parsePostType

parseDelayedType :: (QModeSpec m) => QParser (QType m)
parseDelayedType =
  parseSuspCommon TySusp parseAtomicType parseType
  <|> parseForceCommon TyForce parseAtomicType

parsePostType :: (QModeSpec m) => QParser (QType m)
parsePostType =
  liftA2 (foldl' (flip ($))) parseTupleArgDataType (many parsePostOp)
  where
    parsePostOp =
      choice
        [ keyword "Up" $> flip TyUp Seq.empty <*> parseMode <?> "Upshift of the type"
        , keyword "Down" $> TyDown <*> parseMode <?> "Downshift of the type"
        , keyword "Array" $> TyArray <?> "Array of the type"
        , flip (TyData . pure) <$> parseUpperId <?> "type constructor"
        ]

parseTupleArgDataType :: (QModeSpec m) => QParser (QType m)
parseTupleArgDataType = do
  neTys <- pure <$> parseUnitType <|> parened (CMCNE.sepBy1 parseType (symbol ","))
  case neTys of
    ty :| [] -> option ty (TyData [ty] <$> parseUpperId <?> "type constructor")
    _        -> TyData (NE.toList neTys) <$> parseUpperId <?> "type constructor"

parseAtomicType :: (QModeSpec m) => QParser (QType m)
parseAtomicType =
  parseUnitType
  <|> parened parseType
  <?> "type"

parseUnitType :: (QModeSpec m) => QParser (QType m)
parseUnitType =
  choice
    [ keyword "Int" $> TyInt <*> parseMode
    , keyword "Bool" $> TyBool <*> parseMode
    , parseContextualUpCommon TyUp parseType
    , TyVar <$> parseLowerId <?> "type variable"
    , TyData [] <$> parseUpperId <?> "type constructor"
    ]

parseContextualUpCommon :: (QModeSpec m) => (m -> QContext m -> f m -> f m) -> QParser (f m) -> QParser (f m)
parseContextualUpCommon cons p = bracketed parseContextualCommon <*> (keyword "Up" *> parseMode)
  where
    parseContextualCommon = liftA2 (curry (flip (uncurry . cons))) parseContext (symbol "|-" *> p)

parseSuspCommon :: (QModeSpec m) => (QContextHat m -> f m -> f m) -> QParser (f m) -> QParser (f m) -> QParser (f m)
parseSuspCommon cons ap p = keyword "susp" *> parseOpenItem
  where
    parseOpenItem = cons Seq.empty <$> try ap <|> parened (liftA2 cons parseContextHat (symbol "." *> p))

parseForceCommon :: (QModeSpec m) => (f m -> QSubst m -> f m) -> QParser (f m) -> QParser (f m)
parseForceCommon cons ap = keyword "force" *> liftA2 cons ap (option Empty (symbol "@" *> parseSubst))

parseContext :: (QModeSpec m) => QParser (QContext m)
parseContext = Seq.fromList <$> impl <?> "context"
  where
    impl =
      symbol "." *> many (symbol "," *> parseContextItem)
      <|> sepBy1 parseContextItem (symbol ",")

    parseContextItem = liftA2 (,) parseLowerId (symbol ":" *> parseContextEntry)

parseContextEntry :: (QModeSpec m) => QParser (QContextEntry m)
parseContextEntry =
  try (CEKind <$> parseKind)
  <|> CEType <$> parseType

parseContextHat :: QParser (QContextHat m)
parseContextHat = Seq.fromList <$> impl
  where
    impl =
      symbol "." *> many (symbol "," *> parseLowerId)
      <|> sepBy1 parseLowerId (symbol ",")

parseSubst :: (QModeSpec m) => QParser (QSubst m)
parseSubst = fmap Seq.fromList . parened $ sepBy (SEAmbi <$> parseAmbi) (symbol ",")

parseOptAnn :: (a -> c) -> (a -> b -> c) -> QParser a -> QParser b -> QParser c
parseOptAnn f0 fAnn mainp annp = mainp <**> option f0 (flip fAnn <$> annp)

parseMode :: (QModeSpec m) => QParser m
parseMode = impl <?> "mode"
  where
    impl = do
      modeText <- angled (takeWhile1P (Just "mode") (/= '>'))
      case readModeEither (T.unpack modeText) of
        Right m -> pure m
        Left  e -> fail ("invalid mode: " <> e)

parseLowerId :: QParser QId
parseLowerId = qId <$> lowerIdentifier

parseUpperId :: QParser QId
parseUpperId = qId <$> upperIdentifier

------------------------------------------------------------
-- lexer-like combinators
------------------------------------------------------------

toplevelDelimiter :: QParser ()
toplevelDelimiter = symbol ";;" <?> "top-level delimiter \";;\""

keywords :: [Text]
keywords =
  [ "Type"
  , "Array"
  , "Up"
  , "Down"
  , "Int"
  , "Bool"
  , "alloc"
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
  , "data"
  , "of"
  , "require"
  ]

parened :: QParser a -> QParser a
parened = between (symbol "(") (symbol ")")

bracketed :: QParser a -> QParser a
bracketed = between (symbol "[") (symbol "]")

angled :: QParser a -> QParser a
angled = between (symbol "<") (symbol ">")

symbol :: Text -> QParser ()
symbol txt = void (lexeme (MPC.string txt)) <?> ("symbol " <> show txt)

keyword :: Text -> QParser ()
keyword txt
  | txt `elem` keywords = lexeme (try $ MPC.string txt *> notFollowedBy restIdChar) <?> ("keyword " <> show txt)
  | otherwise           = error $ "Parser bug: unknown keyword " <> show txt

lowerIdentifier :: QParser Text
lowerIdentifier = identifierOf MPC.lowerChar <?> "identifier starting with a lower-case letter"

upperIdentifier :: QParser Text
upperIdentifier = identifierOf MPC.upperChar <?> "identifier starting with an upper-case letter"

identifierOf :: QParser Char -> QParser Text
identifierOf firstChar = identifierImpl
  where
    identifierImpl :: QParser Text
    identifierImpl = try . withCondition (`notElem` keywords) ((<> "") . show) $
      lexeme ((T.pack .). (:) <$> firstChar <*> many restIdChar)

restIdChar :: QParser Char
restIdChar = MPC.alphaNumChar <|> oneOf ("_'" :: String) <?> "identifier character"

lexeme :: QParser a -> QParser a
lexeme p = p <* space

space :: QParser ()
space = hidden (MPCL.space MPC.space1 (MPCL.skipLineComment "--") (MPCL.skipBlockCommentNested "{-" "-}"))

withCondition :: (a -> Bool) -> (a -> String) -> QParser a -> QParser a
withCondition cond mkMsg p = do
  o <- getOffset
  r <- p
  if cond r
  then return r
  else region (setErrorOffset o) (fail (mkMsg r))

sepStartBy :: QParser a -> QParser sep -> QParser [a]
sepStartBy p sep = option [] (sepStartBy1 p sep)

sepStartBy1 :: QParser a -> QParser sep -> QParser [a]
sepStartBy1 p sep = optional sep *> sepBy1 p sep
