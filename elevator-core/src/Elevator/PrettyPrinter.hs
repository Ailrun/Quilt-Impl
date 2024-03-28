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

instance (ElModeSpec m) => Pretty (ElContextEntry m) where
  pretty = prettyContextEntry

prettyContextEntry :: (ElModeSpec m) => ElContextEntry m -> Doc ann
prettyContextEntry = undefined

prettyContext :: (ElModeSpec m) => ElContext m -> Doc ann
prettyContext = prettyList

instance (ElModeSpec m) => Pretty (ElType m) where
  pretty = prettyType 0

prettyType :: (ElModeSpec m) => Int -> ElType m -> Doc ann
prettyType _ (TyInt k) = "Int" <+> prettyMode k
prettyType _ (TyBool k) = "Bool" <+> prettyMode k
prettyType p (TyUp k [] ty) = parensIf (p > 1) $ prettyType 2 ty <+> "Up" <+> prettyMode k
prettyType p (TyUp k ctx ty) = parensIf (p > 1) $ brackets (pretty ctx <+> "." <+> pretty ty) <+> "Up" <+> prettyMode k
prettyType p (TyDown k ty) = parensIf (p > 1) $ prettyType 2 ty <+> "Down" <+> prettyMode k
prettyType p (TyArr ty0 ty1) = parensIf (p > 0) $ prettyType 1 ty0 <+> "->" <+> prettyType 0 ty1

instance (ElModeSpec m) => Pretty (ElTerm m) where
  pretty = prettyTerm 0

prettyTerm :: (ElModeSpec m) => Int -> ElTerm m -> Doc ann
prettyTerm _ (TmVar x) = pretty x
prettyTerm _ TmTrue = "true"
prettyTerm _ TmFalse = "false"
prettyTerm p (TmIte t t0 t1) =
  parensIf (p > 9)
  . align
  $ vsep
    [ "if" <+> pretty t
    , "then" <+> pretty t0
    , "else" <+> pretty t1
    ]
prettyTerm _ (TmInt n) = pretty n
prettyTerm p (TmData x ts) = parensIf (p > 10) . hang 2 $ pretty x <> softline <> group (parens (sep (punctuate "," (pretty <$> ts))))
-- prettyTerm p (TmNatCase t tz x ts) =
--   parensIf (p > 0)
--   $ vsep
--   [ nest 2
--     $ vsep
--       [ "case" <+> pretty t <+> "of"
--       , "| 0 ->" <+> pretty tz
--       , "| succ" <+> pretty x <+> "->" <+> pretty ts
--       ]
--   , "end"
--   ]
prettyTerm p (TmBinOp bop t0 t1) = parensIf (p > p') . hang 2 $ align (prettyTerm lp t0) <+> pretty bop <+> align (prettyTerm rp t1)
  where
    (p', lp, rp) = precedenceBinOp bop
prettyTerm p (TmSusp ctxh t) = parensIf (p > 10) . hang 2 $ "susp" <> softline <> group (prettyTerm 11 t)
prettyTerm p (TmForce t sub) = parensIf (p > 10) . hang 2 $ "force" <> softline <> group (prettyTerm 11 t)
prettyTerm p (TmStore t) = parensIf (p > 10) . hang 2 $ "store" <> softline <> group (prettyTerm 11 t)
prettyTerm p (TmMatch t mayTy [(PatLoad pat, t0)]) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest 2
      $ fillSep
        [ "load" <> pretty pat <+> "="
        , pretty t
        ]
    , "in" <+> pretty t0
    ]
prettyTerm p (TmMatch t mayTy [(pat, t0)]) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest 2
      $ fillSep
        [ "let" <> pretty pat <+> "="
        , pretty t
        ]
    , "in" <+> pretty t0
    ]
prettyTerm p (TmMatch t mayTy branches) = undefined
  -- parensIf (p > 0)
  -- . align
  -- $ vsep
  --   [ nest 2
  --     $ fillSep
  --       [ "let" <> pretty pat <+> "="
  --       , pretty t
  --       ]
  --   , "in" <+> pretty t0
  --   ]
prettyTerm p (TmAmbiLam x mayEntry t) =
  parensIf (p > 0)
  . align
  . nest 2
  $ fillSep
    [ "fun" <+> prettyParams params <+> "->"
    , group $ pretty t
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

instance (ElModeSpec m) => Pretty (ElITerm m) where
  pretty = prettyTerm 0 . fromInternal

instance (ElModeSpec m) => Pretty (ElPattern m) where
  pretty = prettyPattern 0

prettyPattern :: (ElModeSpec m) => Int -> ElPattern m -> Doc ann
prettyPattern = undefined

instance (ElModeSpec m) => Pretty (ElAmbi m) where
  pretty = prettyAmbi 0

prettyAmbi :: (ElModeSpec m) => Int -> ElAmbi m -> Doc ann
prettyAmbi p (AmTerm t) = prettyTerm p t
prettyAmbi p (AmType ty) = prettyType p ty
prettyAmbi p (AmCore a) = prettyTerm p (ambiCore2term a)

instance (ElModeSpec m) => Pretty (ElAmbiCore m) where
  pretty = pretty . ambiCore2term

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  d = parens d
parensIf False d = d

prettyParam :: (ElModeSpec m) => (ElPattern m, Maybe (ElContextEntry m)) -> Doc ann
prettyParam (x, Just ty) = parens (pretty x <+> colon <+> pretty ty)
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
