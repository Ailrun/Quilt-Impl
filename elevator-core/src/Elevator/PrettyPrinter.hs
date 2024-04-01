{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Elevator.PrettyPrinter where

import Data.String                 (IsString (fromString))
import Elevator.ModeSpec
import Elevator.Syntax
import Prettyprinter
import Prettyprinter.Render.String (renderString)

showDoc :: Int -> Doc () -> String
showDoc n = renderString . layoutSmart (defaultLayoutOptions { layoutPageWidth = AvailablePerLine n 1})

showPretty :: (Pretty a) => Int -> a -> String
showPretty n = showDoc n . pretty

showPrettyIndent :: (Pretty a) => Int -> Int -> a -> String
showPrettyIndent n m = showDoc n . indent m . pretty

instance (ElModeSpec m) => Pretty (ElTop m) where
  pretty = prettyTop

prettyTop :: (ElModeSpec m) => ElTop m -> Doc ann
prettyTop (TopTmDef x ty t) = pretty x <+> colon <+> pretty ty <+> equals <> group (softline <> pretty t)
prettyTop (TopTyDef ys x m cons) = "data" <+> parens (prettyContextHat ys) <+> pretty x <> prettyMode m <> group (softline <> equals <+> vsepWith "|" (fmap prettyCon cons))
  where
    prettyCon (c, tys) = pretty c <+> "of" <+> prettyProdLike 1 tys

instance (ElModeSpec m) => Pretty (ElKind m) where
  pretty = prettyKind 0

prettyKind :: (ElModeSpec m) => Int -> ElKind m -> Doc ann
prettyKind _ (KiType k) = "Type" <> prettyMode k
prettyKind p (KiUp k [] ki) = parensIf (p > 1) $ prettyKind 2 ki <+> "Up" <> prettyMode k
prettyKind p (KiUp k ctx ki) = parensIf (p > 1) $ brackets (prettyContext ctx <+> turnstile <+> pretty ki) <+> "Up" <> prettyMode k

instance (ElModeSpec m) => Pretty (ElType m) where
  pretty = prettyType 0

prettyType :: (ElModeSpec m) => Int -> ElType m -> Doc ann
prettyType _ (TyVar x) = pretty x
prettyType _ (TyInt k) = "Int" <> prettyMode k
prettyType _ (TyBool k) = "Bool" <> prettyMode k
prettyType _ (TyProd tys) = prettyProdLike 1 tys
prettyType _ (TyData [] x) = pretty x
prettyType p (TyData [ty] x) = parensIf (p > 1) $ prettyType 2 ty <+> pretty x
prettyType p (TyData tys x) = parensIf (p > 1) $ prettyProdLike 1 tys <+> pretty x
prettyType p (TyUp k [] ty) = parensIf (p > 1) $ prettyType 2 ty <+> "Up" <> prettyMode k
prettyType p (TyUp k ctx ty) = parensIf (p > 1) $ brackets (prettyContext ctx <+> turnstile <+> pretty ty) <+> "Up" <> prettyMode k
prettyType p (TyDown k ty) = parensIf (p > 1) $ prettyType 2 ty <+> "Down" <> prettyMode k
prettyType p (TySusp [] ty) = parensIf (p > 1) $ "susp" <+> prettyType 2 ty
prettyType p (TySusp ctxh ty) = parensIf (p > 1) $ "susp" <+> parens (prettyContextHat ctxh <+> dot <+> pretty ty)
prettyType p (TyForce ty []) = parensIf (p > 1) $ "force" <+> prettyType 2 ty
prettyType p (TyForce ty sub) = parensIf (p > 1) $ "force" <+> prettyType 2 ty <> softline <> nest 2 ("with" <+> prettyTupleLike 0 sub)
prettyType p (TyArr ty0 ty1) = parensIf (p > 0) $ prettyType 1 ty0 <+> singlearrow <+> prettyType 0 ty1
prettyType p (TyForall a ki0 ty1) = parensIf (p > 0) $ parens (pretty a <+> colon <+> pretty ki0) <+> singlearrow <+> prettyType 0 ty1

prettyProdLike :: (ElModeSpec m) => Int -> [ElType m] -> Doc ann
prettyProdLike p = group . parens . vsepWith "*" . fmap (prettyType p)

prettyTypeAnn :: (ElModeSpec m) => Maybe (ElType m) -> Doc ann
prettyTypeAnn (Just ty) = space <> colon <+> pretty ty
prettyTypeAnn Nothing   = emptyDoc

instance (ElModeSpec m) => Pretty (ElContextEntry m) where
  pretty = prettyContextEntry

prettyContextEntry :: (ElModeSpec m) => ElContextEntry m -> Doc ann
prettyContextEntry (EntryOfKi ki) = pretty ki
prettyContextEntry (EntryOfTy ty) = pretty ty

prettyContext :: (ElModeSpec m) => ElContext m -> Doc ann
prettyContext = group . vsepWith comma . fmap (\(x, entry) -> pretty x <> colon <> pretty entry)

prettyContextHat :: ElContextHat m -> Doc ann
prettyContextHat = vsepWith comma . fmap pretty

instance (ElModeSpec m) => Pretty (ElTerm m) where
  pretty = prettyTerm 0

prettyTerm :: (ElModeSpec m) => Int -> ElTerm m -> Doc ann
prettyTerm _ (TmVar x) = pretty x
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
prettyTerm p (TmSusp [] t) = parensIf (p > 10) . hang 2 $ "susp" <+> prettyTerm 11 t
prettyTerm p (TmSusp ctxh t) = parensIf (p > 10) . hang 2 $ "susp" <+> parens (prettyContextHat ctxh <+> dot <+> pretty t)
prettyTerm p (TmForce t []) = parensIf (p > 10) . hang 2 $ "force" <+> prettyTerm 11 t
prettyTerm p (TmForce t sub) = parensIf (p > 10) . hang 2 $ "force" <+> prettyTerm 11 t <> softline <> "with" <+> prettyTupleLike 0 sub
prettyTerm p (TmStore t) = parensIf (p > 10) . hang 2 $ "store" <> softline <> prettyTerm 11 t
prettyTerm p (TmMatch t mayTy [(PatLoad pat, t0)]) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest 2
      $ fillSep
        [ "load" <> pretty pat <> prettyTypeAnn mayTy <+> equals
        , pretty t
        ]
    , "in" <+> pretty t0
    , "end"
    ]
prettyTerm p (TmMatch t mayTy [(pat, t0)]) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest 2
      $ fillSep
        [ "let" <> pretty pat <> prettyTypeAnn mayTy <+> equals
        , pretty t
        ]
    , "in" <+> pretty t0
    , "end"
    ]
prettyTerm p (TmMatch t mayTy branches) =
  parensIf (p > 0)
  $ vsep
  [ nest 2
    $ vsep
      ("match" <+> pretty t <> prettyTypeAnn mayTy <+> "with"
       : fmap (\(pati, ti) -> pipe <+> pretty pati <+> doublearrow <+> pretty ti) branches)
  , "end"
  ]
prettyTerm p (TmAmbiLam x mayEntry t) =
  parensIf (p > 0)
  . align
  . nest 2
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
  . nest 2
  $ fillSep
    [ prettyTerm 10 t0
    , prettyAmbi 11 a1
    ]
prettyTerm p (TmAnn t ty) =
  parensIf (p > 0)
  . nest 2
  $ fillSep
    [ prettyTerm 1 t
    , colon <+> prettyType 0 ty
    ]

prettyTupleLike :: (ElModeSpec m) => Int -> [ElTerm m] -> Doc ann
prettyTupleLike p = group . parens . vsepWith comma . fmap (prettyTerm p)

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
vsepWith d = concatWith (surround (d <> softline))

turnstile :: Doc ann
turnstile = "|-"

underscore :: Doc ann
underscore = "_"

singlearrow :: Doc ann
singlearrow = "->"

doublearrow :: Doc ann
doublearrow = "=>"
