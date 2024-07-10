{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Elevator.PrettyPrinter where

import Data.Sequence               (Seq (Empty))
import Data.String                 (IsString (fromString))
import Prettyprinter
import Prettyprinter.Render.String (renderString)

import Data.Foldable               (Foldable (toList))
import Data.HashMap.Strict         qualified as HashMap
import Elevator.Evaluator          (ElEnv (..), ElEvalError (..))
import Elevator.ModeSpec
import Elevator.Substitution       (ElSubstError (..))
import Elevator.Syntax
import Elevator.TypeChecker        (ElTypingEnvironment (..),
                                    ElTypingEnvironmentEntry (..),
                                    ElTypingError (..),
                                    ElTypingErrorModeOrdering (..),
                                    ElTypingErrorTarget (..))

showDoc :: Int -> Doc () -> String
showDoc n = renderString . layoutSmart (defaultLayoutOptions { layoutPageWidth = AvailablePerLine n 1})

showPretty :: (Pretty a) => Int -> a -> String
showPretty n = showDoc n . pretty

showPrettyIndent :: (Pretty a) => Int -> Int -> a -> String
showPrettyIndent n m = showDoc n . indent m . pretty

showPrettyMode :: (ElModeSpec m) => Int -> m -> String
showPrettyMode n = showDoc n . prettyMode

showPrettyError :: (Pretty err) => Int -> Maybe Integer -> err -> String
showPrettyError n (Just l) err = showDoc n $ "Error <interactive line" <+> pretty l <> ">:" <> nest indentSize (hardline <> pretty err)
showPrettyError n Nothing err = showDoc n $ "Error:" <> nest indentSize (hardline <> pretty err)

showPrettyEnv :: (ElModeSpec m) => Int -> ElEnv m -> String
showPrettyEnv n env = showDoc n $ nest indentSize (hardline <> prettyEnv env)

instance (ElModeSpec m) => Pretty (ElTop m) where
  pretty = prettyTop

prettyTop :: (ElModeSpec m) => ElTop m -> Doc ann
prettyTop (TopTermDef x ty t)      = pretty x <+> colon <+> pretty ty <+> equals <> groupedNestOnNextLine (pretty t)
prettyTop (TopTypeDef ys x m cons) = "data" <+> parens (prettyTyArgs ys) <+> pretty x <> prettyMode m <> groupedNestOnNextLine (equals <+> vsepWith "|" (fmap prettyCon cons))
  where
    prettyTyArgs = vsepWith comma . fmap prettyTyArg
    prettyTyArg (y, mayKi) = pretty y <+> prettyKindAnn mayKi
    prettyCon (c, tys) = pretty c <+> "of" <+> prettyProdLike 2 tys

instance (ElModeSpec m) => Pretty (ElKind m) where
  pretty = prettyKind 0

prettyKind :: (ElModeSpec m) => Int -> ElKind m -> Doc ann
prettyKind _ (KiType k)        = "Type" <> prettyMode k
prettyKind p (KiUp k Empty ki) = parensIf (p > 1) $ prettyKind 2 ki <+> "Up" <> prettyMode k
prettyKind p (KiUp k ctx ki)   = parensIf (p > 1) $ brackets (prettyContext ctx <+> turnstile <+> pretty ki) <+> "Up" <> prettyMode k

prettyKindAnn :: (ElModeSpec m) => Maybe (ElKind m) -> Doc ann
prettyKindAnn (Just ki) = space <> colon <+> pretty ki
prettyKindAnn Nothing   = emptyDoc

instance (ElModeSpec m) => Pretty (ElType m) where
  pretty = prettyType 0

prettyType :: (ElModeSpec m) => Int -> ElType m -> Doc ann
prettyType _ (TyVar x) = pretty x
prettyType _ (TyInt k) = "Int" <> prettyMode k
prettyType _ (TyBool k) = "Bool" <> prettyMode k
prettyType _ (TyProd tys) = prettyProdLike 2 tys
prettyType _ (TyData [] x) = pretty x
prettyType p (TyData [ty] x) = parensIf (p > 2) $ prettyType 3 ty <+> pretty x
prettyType p (TyData tys x) = parensIf (p > 2) $ prettyProdLike 2 tys <+> pretty x
prettyType p (TyArray ty) = parensIf (p > 2) $ prettyType 3 ty <+> "Array"
prettyType p (TyUp k Empty ty) = parensIf (p > 2) $ prettyType 3 ty <+> "Up" <> prettyMode k
prettyType p (TyUp k ctx ty) = parensIf (p > 2) $ brackets (prettyContext ctx <+> turnstile <+> pretty ty) <+> "Up" <> prettyMode k
prettyType p (TyDown k ty) = parensIf (p > 2) $ prettyType 3 ty <+> "Down" <> prettyMode k
prettyType p (TySusp Empty ty) = parensIf (p > 2) $ "susp" <+> prettyType 3 ty
prettyType p (TySusp ctxh ty) = parensIf (p > 2) $ "susp" <+> parens (prettyContextHat ctxh <+> dot <+> pretty ty)
prettyType p (TyForce ty Empty) = parensIf (p > 2) $ "force" <+> prettyType 3 ty
prettyType p (TyForce ty sub) = parensIf (p > 2) $ "force" <+> prettyType 3 ty <> groupedNestOnNextLine ("@" <+> prettySubst sub)
prettyType p (TyArr ty0 ty1) = parensIf (p > 1) $ prettyType 2 ty0 <+> singlearrow <+> prettyType 1 ty1
prettyType p (TyForall a ki0 ty1) = parensIf (p > 1) $ parens (pretty a <+> colon <+> pretty ki0) <+> singlearrow <+> prettyType 1 ty1
prettyType p (TyAnn ty ki) =
  parensIf (p > 0)
  . nest indentSize
  $ fillSep
    [ prettyType 1 ty
    , colon <+> pretty ki
    ]

prettyProdLike :: (Functor t, Foldable t, ElModeSpec m) => Int -> t (ElType m) -> Doc ann
prettyProdLike p = group . parens . vsepWith "*" . fmap (prettyType p)

prettyTypeAnn :: (ElModeSpec m) => Maybe (ElType m) -> Doc ann
prettyTypeAnn (Just ty) = space <> colon <+> pretty ty
prettyTypeAnn Nothing   = emptyDoc

instance (ElModeSpec m) => Pretty (ElContextEntry m) where
  pretty = prettyContextEntry

prettyContextEntry :: (ElModeSpec m) => ElContextEntry m -> Doc ann
prettyContextEntry (CEKind ki) = pretty ki
prettyContextEntry (CEType ty) = pretty ty

prettyContext :: (ElModeSpec m) => ElContext m -> Doc ann
prettyContext = group . vsepWith comma . fmap (\(x, entry) -> pretty x <> colon <> pretty entry)

prettyContextHat :: ElContextHat m -> Doc ann
prettyContextHat = vsepWith comma . fmap pretty

instance (ElModeSpec m) => Pretty (ElTerm m) where
  pretty = prettyTerm 0

prettyTerm :: (ElModeSpec m) => Int -> ElTerm m -> Doc ann
prettyTerm _ (TmVar x) = pretty x
prettyTerm _ (TmArrayTag n) = "<array@" <> pretty n <> ">"
prettyTerm _ (TmBuiltIn bi) = pretty (fromBuiltIn bi)
prettyTerm _ TmTrue = "True"
prettyTerm _ TmFalse = "False"
prettyTerm p (TmIte t t0 t1) =
  parensIf (p > 9)
  . align
  $ vsep
    [ "if" <+> pretty t
    , "then" <+> pretty t0
    , "else" <+> pretty t1
    ]
prettyTerm _ (TmInt n) = pretty n
prettyTerm p (TmBinOp bop t0 t1) = parensIf (p > p') . hang 2 $ align (prettyTerm lp t0) <+> pretty bop <+> align (prettyTerm rp t1)
  where
    (p', lp, rp) = precedenceBinOp bop
prettyTerm _ (TmTuple ts) = prettyTupleLike 0 ts
prettyTerm p (TmData x ts) = parensIf (p > 10) . hang 2 $ pretty x <> softline <> prettyTupleLike 0 ts
prettyTerm p (TmSusp Empty t) = parensIf (p > 10) . hang 2 $ "susp" <+> prettyTerm 11 t
prettyTerm p (TmSusp ctxh t) = parensIf (p > 10) . hang 2 $ "susp" <+> parens (prettyContextHat ctxh <+> dot <+> pretty t)
prettyTerm p (TmForce t Empty) = parensIf (p > 10) . hang 2 $ "force" <+> prettyTerm 11 t
prettyTerm p (TmForce t sub) = parensIf (p > 10) . hang 2 $ "force" <+> prettyTerm 11 t <> softline <> "@" <+> prettySubst sub
prettyTerm p (TmStore t) = parensIf (p > 10) . hang 2 $ "store" <> softline <> prettyTerm 11 t
prettyTerm p (TmMatch t mayTy [(PatLoad pat, t0)]) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest indentSize
      $ fillSep
        [ "load" <+> pretty pat <> prettyTypeAnn mayTy <+> equals
        , pretty t
        ]
    , "in" <+> pretty t0
    , "end"
    ]
prettyTerm p (TmMatch t mayTy [(pat, t0)]) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest indentSize
      $ fillSep
        [ "let" <+> pretty pat <> prettyTypeAnn mayTy <+> equals
        , pretty t
        ]
    , "in" <+> pretty t0
    , "end"
    ]
prettyTerm p (TmMatch t mayTy branches) =
  parensIf (p > 0)
  $ vsep
  [ nest indentSize
    $ vsep
      ("match" <+> pretty t <> prettyTypeAnn mayTy <+> "with"
       : fmap (\(pati, ti) -> pipe <+> pretty pati <+> doublearrow <+> pretty ti) branches)
  , "end"
  ]
prettyTerm p (TmAmbiLam x mayEntry t) =
  parensIf (p > 0)
  . align
  . nest indentSize
  $ fillSep
    [ "fun" <+> prettyParams params <+> singlearrow
    , group (pretty t)
    ]
  where
    params = (x, mayEntry) : getParams t

    getParams (TmAmbiLam x' mayEntry' t') = (x', mayEntry') : getParams t'
    getParams _                           = []
prettyTerm p (TmAmbiApp t0 a1) =
  parensIf (p > 10)
  . nest indentSize
  $ fillSep
    [ prettyTerm 10 t0
    , prettyAmbi 11 a1
    ]
prettyTerm p (TmAnn t ty) =
  parensIf (p > 0)
  . nest indentSize
  $ fillSep
    [ prettyTerm 1 t
    , colon <+> pretty ty
    ]

prettyTupleLike :: (Functor t, Foldable t, ElModeSpec m) => Int -> t (ElTerm m) -> Doc ann
prettyTupleLike p = group . parens . vsepWith comma . fmap (prettyTerm p)

instance (ElModeSpec m) => Pretty (ElSubstEntry m) where
  pretty = prettySubstEntry

prettySubstEntry :: (ElModeSpec m) => ElSubstEntry m -> Doc ann
prettySubstEntry (SEAmbi am) = pretty am

prettySubst :: (ElModeSpec m) => ElSubst m -> Doc ann
prettySubst = tupled . toList . fmap pretty

instance (ElModeSpec m) => Pretty (ElIContextEntry m) where
  pretty = prettyContextEntry . fromInternal

instance (ElModeSpec m) => Pretty (ElIKind m) where
  pretty = prettyKind 0 . fromInternal

instance (ElModeSpec m) => Pretty (ElIType m) where
  pretty = prettyType 0 . fromInternal

instance (ElModeSpec m) => Pretty (ElITerm m) where
  pretty = prettyTerm 0 . fromInternal

instance (ElModeSpec m) => Pretty (ElPattern m) where
  pretty = prettyPattern 0

prettyPattern :: (ElModeSpec m) => Int -> ElPattern m -> Doc ann
prettyPattern _ PatWild = underscore
prettyPattern _ (PatVar x) = pretty x
prettyPattern _ PatTrue = "True"
prettyPattern _ PatFalse = "False"
prettyPattern _ (PatInt i) = pretty i
prettyPattern _ (PatTuple pats) = prettyPatternTupleLike 0 pats
prettyPattern p (PatLoad pat) = parensIf (p > 0) $ "load" <+> prettyPattern 1 pat
prettyPattern _ (PatData x []) = pretty x
prettyPattern p (PatData x [t]) = parensIf (p > 0) $ pretty x <+> prettyPattern 1 t
prettyPattern p (PatData x ts) = parensIf (p > 0) $ pretty x <+> prettyPatternTupleLike 0 ts

prettyPatternTupleLike :: (ElModeSpec m) => Int -> [ElPattern m] -> Doc ann
prettyPatternTupleLike p = group . parens . vsepWith comma . fmap (prettyPattern p)

instance (ElModeSpec m) => Pretty (ElIPattern m) where
  pretty = prettyPattern 0 . fromInternal

instance Pretty ElBinOp where
  pretty = prettyBinOp

prettyBinOp :: ElBinOp -> Doc ann
prettyBinOp OpAdd = "+"
prettyBinOp OpSub = "-"
prettyBinOp OpMul = "*"
prettyBinOp OpDiv = "/"
prettyBinOp OpMod = "%"
prettyBinOp OpEq  = "=="
prettyBinOp OpNe  = "/="
prettyBinOp OpLe  = "<="
prettyBinOp OpLt  = "<"
prettyBinOp OpGe  = ">="
prettyBinOp OpGt  = ">"

instance (ElModeSpec m) => Pretty (ElAmbi m) where
  pretty = prettyAmbi 0

prettyAmbi :: (ElModeSpec m) => Int -> ElAmbi m -> Doc ann
prettyAmbi p (AmTerm t)  = prettyTerm p t
prettyAmbi p (AmType ty) = prettyType p ty
prettyAmbi p (AmCore a)  = prettyTerm p (ambiCore2term a)

instance (ElModeSpec m) => Pretty (ElAmbiCore m) where
  pretty = pretty . ambiCore2term

instance (ElModeSpec m) => Pretty (ElTypingError m) where
  pretty = prettyTypingError

prettyTypingError :: (ElModeSpec m) => ElTypingError m -> Doc ann
prettyTypingError (TESubstitutionError se) = pretty se
prettyTypingError (TESubstitutionEntryClassMismatchForType x t _) = "Type variable" <> groupedNestOnNextLine (dquotes (pretty x)) <> "cannot be instantiated with a term, but this term is provided:" <> groupedNestOnNextLine (pretty t)
prettyTypingError (TESubstitutionEntryClassMismatchForTerm x ty _) = "Term variable" <+> pretty x <+> "cannot be instantiated with a type, but this type is provided:" <> groupedNestOnNextLine (pretty ty)
prettyTypingError (TEInvalidNonTypeKind iki) = "Kind" <> groupedNestOnNextLine (pretty iki) <> "is not the kind Type for some mode"
prettyTypingError (TENotInContext x ictx) = "Variable" <> groupedNestOnNextLine (dquotes (pretty x)) <> "is not found in the context:" <> groupedNestOnNextLine (prettyContext (icontext2context ictx))
prettyTypingError (TENotInEnvironment x env) = "Variable" <> groupedNestOnNextLine (dquotes (pretty x)) <> "is not found in the environment:" <> groupedNestOnNextLine (prettyTypingEnvironment env)
prettyTypingError (TETypeVariableAsTerm x) = "Type variable" <> groupedNestOnNextLine (dquotes (pretty x)) <> "cannot be used as a term"
prettyTypingError (TETermVariableAsType x) = "Term variable" <> groupedNestOnNextLine (dquotes (pretty x)) <> "cannot be used as a type"
prettyTypingError (TEVariableClassMismatch x) = "Variable" <> groupedNestOnNextLine (dquotes (pretty x)) <> "cannot be used as a type and a term"
prettyTypingError TEInvalidEmptyProd = "Nullary product type is not allowed"
prettyTypingError (TEInvalidKindForSusp iki) = "Type construct susp must have a template kind, but this kind is provided:" <> groupedNestOnNextLine (pretty iki)
prettyTypingError (TEInvalidTypeBodyForForce ity iki) = "Type construct force cannot use this type:" <> groupedNestOnNextLine (pretty ity) <> "as it has this non-template kind:" <> groupedNestOnNextLine (pretty iki)
prettyTypingError TEInvalidKindTypeForSusp = "Type construct susp cannot have a kind Type"
prettyTypingError (TEInvalidTypeForData ity) = "Data constructor must have a datatype, but this type is provided:" <> groupedNestOnNextLine (pretty ity) <> "cannot be used for a "
prettyTypingError (TEInvalidTypeForTrue ity) = "Term True must have a Bool type, but this type is provided:" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TEInvalidTypeForFalse ity) = "Term False must have a Bool type, but this type is provided:" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TEInvalidTypeForInt ity) = "An int term must have an Int type, but this type is provided:" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TEInvalidTypeForTuple ity) = "A tuple must have a product type, but this type is provided:" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TEInvalidTypeForSusp ity) = "Term construct susp must have a template type" <> groupedNestOnNextLine (pretty ity) <> "cannot be used for a susp"
prettyTypingError (TEInvalidTermBodyForForce it ity) = "Term" <> groupedNestOnNextLine (pretty it) <> "of a non-template type" <> groupedNestOnNextLine (pretty ity) <> "cannot be forced"
prettyTypingError (TEInvalidTypeForStore ity) = "Term construct store must have a pointer type, but this type is provided:" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TEInvalidPointerTypeForLoad ity) = "A non-pointer type" <> groupedNestOnNextLine (pretty ity) <> "cannot be loaded"
prettyTypingError (TEInvalidTypeForLam ity) = "A function must have a function type, but this type is provided:" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TEInvalidFunctionForApp it ity) = "Term" <> groupedNestOnNextLine (pretty it) <> "of a non-function type" <> groupedNestOnNextLine (pretty ity) <> "cannot be called"
prettyTypingError (TEInvalidConditionForIte it ity) = "Term" <> groupedNestOnNextLine (pretty it) <> "of a non-Bool type" <> groupedNestOnNextLine (pretty ity) <> "cannot be used as a condition of if-then-else expression"
prettyTypingError (TEInvalidTypeArgForLam ty) = "Type" <> groupedNestOnNextLine (pretty ty) <> "cannot be used to call a function expecting a value"
prettyTypingError (TEInvalidTermArgForTypeLam t) = "Term" <> groupedNestOnNextLine (pretty t) <> "cannot be used to call a function expecting a type"
prettyTypingError (TEInvalidKindAnnForLam ki ity) = "Kind" <> groupedNestOnNextLine (pretty ki) <> "cannot be used to annotate a value argument of type" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TEInvalidTypeAnnForTypeLam ty iki) = "Type" <> groupedNestOnNextLine (pretty ty) <> "cannot be used to annotate a type argument of kind" <> groupedNestOnNextLine (pretty iki)
prettyTypingError (TEInvalidPatternForTypeLam pat) = "A type argument cannot be pattern-matched, but this pattern is provided:" <> groupedNestOnNextLine (pretty pat)
prettyTypingError (TEInvalidBuiltIn m bi) = "A built-in primitive" <+> dquotes (pretty (fromBuiltIn bi)) <+> "cannot be used in" <+> prettyMode m
prettyTypingError (TEInvalidTypeForArrayTag ity) = "An array must have an array type, but this type is provided" <> groupedNestOnNextLine (pretty ity)
prettyTypingError (TECheckOnlyTermInInference t) = "The type of the term" <> groupedNestOnNextLine (pretty t) <> "cannot be inferred, as it is only a checkable term." <> hardline <> "Consider to provide a type annotation (term : type) or lift it as a top-level definiltion (with a type signature)"
prettyTypingError (TECheckOnlyTypeInInference ty) = "The kind of the type" <> groupedNestOnNextLine (pretty ty) <> "cannot be inferred, as it is only a checkable type." <> hardline <> "Consider to provide a kind annotation (type : kind)"
prettyTypingError (TEDuplicatedTypeName x) = "Top-level type of name" <> groupedNestOnNextLine (dquotes (pretty x)) <> "already exists"
prettyTypingError (TEDuplicatedConName x c) = "Constructor of name" <> groupedNestOnNextLine (dquotes (pretty c)) <> "already exists in the top-level type of name" <> groupedNestOnNextLine (dquotes (pretty x))
prettyTypingError (TEDuplicatedTermName x) = "Top-level term of name" <> groupedNestOnNextLine (dquotes (pretty x)) <> "already exists"
prettyTypingError (TEUnunifiableIKinds iki iki') = "Two kinds" <> groupedNestOnNextLine (pretty iki) <> "and" <> groupedNestOnNextLine (pretty iki') <> "cannot be unified"
prettyTypingError (TEUnunifiableITypes ity ity') = "Two types" <> groupedNestOnNextLine (pretty ity) <> "and" <> groupedNestOnNextLine (pretty ity') <> "cannot be unified"
prettyTypingError (TEUnunifiableIEntry ice ice') = "Two context entry" <> groupedNestOnNextLine (pretty ice) <> "and" <> groupedNestOnNextLine (pretty ice') <> "cannot be unified"
prettyTypingError (TEContextHatConflict ctxh ictx) = "Variable list" <> groupedNestOnNextLine (prettyContextHat ctxh) <> "cannot be check against context" <> groupedNestOnNextLine (prettyContext (icontext2context ictx)) <> "cannot be unified"
prettyTypingError (TEModeOrderFailure o m m') = "Mode" <+> prettyMode m <+> "is not" <+> prettyModeOrdering o <+> prettyMode m'
prettyTypingError (TEModeNotEqual m m') = "Mode" <+> prettyMode m <+> "and" <+> prettyMode m' <+> "cannot be identical"
prettyTypingError (TEModeStructuralRule r m) = "Mode" <+> prettyMode m <+> "does not allow" <+> prettyModeSt r
prettyTypingError (TENotYetSupported name) = "We do not support " <+> pretty name <+> "yet"
prettyTypingError (TETypeArgNumberMismatch x n argTys) = "Type" <> groupedNestOnNextLine (dquotes (pretty x)) <> "requires" <+> pretty n <+> plural "argument" "arguments" n <> ", but" <> groupedNestOnNextLine (prettyProdLike 0 argTys) <> "are given"
prettyTypingError (TEConstructorArgNumberMismatch x c n args) = "Constructor" <> groupedNestOnNextLine (dquotes (pretty c)) <> "of type" <> groupedNestOnNextLine (dquotes (pretty x)) <> "requires" <+> pretty n <+> plural "argument" "arguments" n <> ", but" <> groupedNestOnNextLine (prettyTupleLike 0 args) <> "are given"
prettyTypingError (TEConstructorPatternArgNumberMismatch x c n pats) = "Constructor pattern for" <> groupedNestOnNextLine (dquotes (pretty c)) <> "of type" <> groupedNestOnNextLine (dquotes (pretty x)) <> "requires" <+> pretty n <+> plural "pattern" "patterns" n <> ", but" <> groupedNestOnNextLine (prettyPatternTupleLike 0 pats) <> "are given"
prettyTypingError (TETupleArgNumberMismatch ity n items) = "Tuple of type" <> groupedNestOnNextLine (pretty ity) <> "requires" <+> pretty n <+> plural "argument" "arguments" n <> ", but" <> groupedNestOnNextLine (prettyTupleLike 0 items) <> "are given"
prettyTypingError (TETuplePatternArgNumberMismatch ity n pats) = "Tuple of type" <> groupedNestOnNextLine (pretty ity) <> "requires" <+> pretty n <+> plural "pattern" "patterns" n <> ", but" <> groupedNestOnNextLine (prettyPatternTupleLike 0 pats) <> "are given"
prettyTypingError (TETooLongSubstitution n sub) = "Target context has only" <+> pretty n <+> plural "variable" "variables" n <> ", but the provided substitution" <+> groupedNestOnNextLine (prettySubst sub) <> "has more entries than that"
prettyTypingError (TERepeatedContextEntryInWeakening ictx) = "Context" <> groupedNestOnNextLine (prettyContext (icontext2context ictx)) <> "of a contextual object has two or more entries with the same name"
prettyTypingError (TEInternalError te) = prettyInternalTypeCheckerBug <> prettyTypingError te
prettyTypingError (TEFor tet te) = pretty te <> hardline <> hardline <> align ("under" <+> pretty tet)
-- prettyTypingError te = pretty $ show te

prettyModeOrdering :: ElTypingErrorModeOrdering -> Doc ann
prettyModeOrdering TEMOGT = "greater than"
prettyModeOrdering TEMOGE = "greater than or equal to"
prettyModeOrdering TEMOLT = "less than"
prettyModeOrdering TEMOLE = "less than or equal to"

prettyModeSt :: ElMdSt -> Doc ann
prettyModeSt MdStWk = "weakening"
prettyModeSt MdStCo = "contraction"

prettyTypingEnvironment :: (ElModeSpec m) => ElTypingEnvironment m -> Doc ann
prettyTypingEnvironment =  group . (<> softline) . vsep . fmap prettyTypingEnvironmentItem . toList . getElTypingEnvironment

prettyTypingEnvironmentItem :: (ElModeSpec m) => (ElId, m, ElTypingEnvironmentEntry m) -> Doc ann
prettyTypingEnvironmentItem (x, _, TEETermDecl ity) = pretty x <+> colon <> groupedNestOnNextLine (pretty ity)
prettyTypingEnvironmentItem (x, k, TEETypeDecl iargKis) = prettyArgKis iargKis <+> pretty x <+> colon <> pretty (KiType k)
  where
    prettyArgKis []       = mempty
    prettyArgKis iargKis' = group . parens . (<> softline') . vsepWith comma $ fmap prettyArgKi iargKis'
    prettyArgKi (a, iki) = pretty a <+> colon <> groupedNestOnNextLine (pretty iki)
prettyTypingEnvironmentItem (c, _, TEEConDecl _ params iargTys d) = pretty c <+> "of" <> groupedNestOnNextLine (prettyArgTys iargTys) <+> colon <> groupedNestOnNextLine (prettyTypeParams params <+> pretty d)
  where
    prettyArgTys []       = mempty
    prettyArgTys [iargTy] = pretty iargTy
    prettyArgTys iargTys' = group . parens . vsepWith (flatAlt "" " " <> "*") $ fmap pretty iargTys'

    prettyTypeParams []      = mempty
    prettyTypeParams [param] = pretty param
    prettyTypeParams params' = tupled $ fmap pretty params'

instance (ElModeSpec m) => Pretty (ElTypingErrorTarget m) where
  pretty = prettyTypingErrorTarget

prettyTypingErrorTarget :: (ElModeSpec m) => ElTypingErrorTarget m -> Doc ann
prettyTypingErrorTarget (TETMode k) = "mode:" <+> prettyMode k
prettyTypingErrorTarget (TETTypeDefinition x) = "top-level type definition:" <> groupedNestOnNextLine (dquotes (pretty x))
prettyTypingErrorTarget (TETTermDefinition x) = "top-level term definition:" <> groupedNestOnNextLine (dquotes (pretty x))
prettyTypingErrorTarget (TETContext ctx) = "context:" <> groupedNestOnNextLine (prettyContext ctx)
prettyTypingErrorTarget (TETKind ki) = "kind:" <> groupedNestOnNextLine (pretty ki)
prettyTypingErrorTarget (TETType ty) = "type:" <> groupedNestOnNextLine (pretty ty)
prettyTypingErrorTarget (TETTerm t) = "term:" <> groupedNestOnNextLine (pretty t)
prettyTypingErrorTarget (TETSubst sub) = "substitution:" <> groupedNestOnNextLine (prettySubst sub)
prettyTypingErrorTarget (TETVariable x) = "variable:" <> groupedNestOnNextLine (dquotes (pretty x))
prettyTypingErrorTarget (TETConstructor c) = "constructor:" <> groupedNestOnNextLine (dquotes (pretty c))

instance (ElModeSpec m) => Pretty (ElEvalError m) where
  pretty = prettyEvalError

prettyEvalError :: (ElModeSpec m) => ElEvalError m -> Doc ann
prettyEvalError (EESubstitutionError se) = pretty se
prettyEvalError (EEVariableNotInEnv x env) = "Variable" <> groupedNestOnNextLine (dquotes (pretty x)) <> "is not in" <> groupedNestOnNextLine (prettyEnv env)
prettyEvalError (EENonBoolean it) = "Non-boolean result" <> groupedNestOnNextLine (pretty it) <> "from the condition of an if-then-else expression"
prettyEvalError (EENonInteger it s) = "Non-integer result" <> groupedNestOnNextLine (pretty it) <> "for" <+> pretty s
prettyEvalError (EENonTemplate it) = "Non-template result" <> groupedNestOnNextLine (pretty it) <> "for a force"
prettyEvalError (EENonFunction it) = "Non-function result" <> groupedNestOnNextLine (pretty it) <> "for a function call"
prettyEvalError (EENonTypeFunction it) = "Non-type-function result" <> groupedNestOnNextLine (pretty it) <> "for a type function call"
prettyEvalError (EENoMatchingClause it) = "No matching clause for" <> groupedNestOnNextLine (pretty it)
prettyEvalError (EESinglePatternMismatch ipat t) = "The scrutinee" <> groupedNestOnNextLine (pretty t) <> "does not match the single pattern" <> groupedNestOnNextLine (pretty ipat)
prettyEvalError (EEInvalidCallForBuiltIn bi ispine) = "Invalid call of" <+> dquotes (pretty (fromBuiltIn bi)) <+> "with" <+> groupedNestOnNextLine (prettySubst (isubst2subst ispine))
prettyEvalError (EEInvalidArgumentOfBuiltIn bi ir s) = "Invalid result" <> groupedNestOnNextLine (pretty ir) <> "for" <+> pretty s <+> "of" <+> dquotes (pretty (fromBuiltIn bi))
prettyEvalError (EEInvalidHeapLoc tag) = "Invalid heap address" <+> pretty tag <+> "is accessed"

prettyEnv :: (ElModeSpec m) => ElEnv m -> Doc ann
prettyEnv = group . vsepWith (flatAlt "" " ...") . fmap prettyEnvEntry . HashMap.toList . getElEnv

prettyEnvEntry :: (ElModeSpec m) => (ElId, Maybe (ElITerm m)) -> Doc ann
prettyEnvEntry (x, Just t) = dquotes (pretty x) <+> "|->" <+> groupedNestOnNextLine (pretty t)
prettyEnvEntry (x, Nothing) = dquotes (pretty x) <+> "|-> ?"

instance (ElModeSpec m) => Pretty (ElSubstError m) where
  pretty = prettySubstError

prettySubstError :: (ElModeSpec m) => ElSubstError m -> Doc ann
prettySubstError (SETypeForTermVariable x ty) = prettyInternalTypeCheckerBug <> "Term variable" <+> pretty x <+> "cannot be instantiated with a type" <> groupedNestOnNextLine (pretty ty)
prettySubstError (SETermForTypeVariable x t) = prettyInternalTypeCheckerBug <> "Type variable" <+> pretty x <+> "cannot be instantiated with a term" <> groupedNestOnNextLine (pretty t)

prettyInternalTypeCheckerBug :: Doc ann
prettyInternalTypeCheckerBug = "-------------------- Type Checker Bug --------------------" <> hardline <> "Please report this bug" <> hardline

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  d = parens d
parensIf False d = d

prettyParam :: (ElModeSpec m) => (ElPattern m, Maybe (ElContextEntry m)) -> Doc ann
prettyParam (x, Just ty) = group . parens $ pretty x <> colon <> pretty ty
prettyParam (x, Nothing) = pretty x

prettyParams :: (ElModeSpec m) => [(ElPattern m, Maybe (ElContextEntry m))] -> Doc ann
prettyParams = vsep . fmap prettyParam

prettyMode :: (ElModeSpec m) => m -> Doc ann
prettyMode = angles . fromString . showMode

precedenceBinOp :: ElBinOp -> (Int, Int, Int)
precedenceBinOp OpAdd = (4, 4, 5)
precedenceBinOp OpSub = (4, 4, 5)
precedenceBinOp OpMul = (5, 5, 6)
precedenceBinOp OpDiv = (5, 5, 6)
precedenceBinOp OpMod = (5, 5, 6)
precedenceBinOp OpEq  = (2, 3, 3)
precedenceBinOp OpNe  = (2, 3, 3)
precedenceBinOp OpLe  = (2, 3, 3)
precedenceBinOp OpLt  = (2, 3, 3)
precedenceBinOp OpGe  = (2, 3, 3)
precedenceBinOp OpGt  = (2, 3, 3)

vsepWith :: Foldable t => Doc ann -> t (Doc ann) -> Doc ann
vsepWith d = concatWith (surround (d <> line))

turnstile :: Doc ann
turnstile = "|-"

underscore :: Doc ann
underscore = "_"

singlearrow :: Doc ann
singlearrow = "->"

doublearrow :: Doc ann
doublearrow = "=>"

groupedNestOnNextLine :: Doc ann -> Doc ann
groupedNestOnNextLine = group . nest indentSize . (softline <>) . (<> softline)

indentSize :: Int
indentSize = 2
