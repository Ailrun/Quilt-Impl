{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module ElevatorExt.LambdaBox.PrettyPrinter where

import           Elevator.PrettyPrinter       (precedenceBinOp)
import           Elevator.Syntax              (ElId)
import           ElevatorExt.LambdaBox.Syntax
import           Prettyprinter

instance Pretty ElxType where
  pretty = prettyType 0

prettyType :: Int -> ElxType -> Doc ann
prettyType _ TyxNat = "Nat"
prettyType _ TyxBool = "Bool"
prettyType p (TyxBox ty) = parensIf (p > 1) $ "Box" <+> prettyType 2 ty
prettyType p (TyxArr ty0 ty1) = parensIf (p > 0) $ prettyType 1 ty0 <+> "->" <+> prettyType 0 ty1

instance Pretty ElxTerm where
  pretty = prettyTerm 0

prettyTerm :: Int -> ElxTerm -> Doc ann
prettyTerm _ (TmxVar x) = pretty x
prettyTerm _ TmxTrue = "true"
prettyTerm _ TmxFalse = "false"
prettyTerm p (TmxIte t t0 t1) =
  parensIf (p > 9)
  . align
  $ vsep
    [ "if" <+> pretty t
    , "then" <+> pretty t0
    , "else" <+> pretty t1
    ]
prettyTerm _ (TmxNat n) = pretty n
prettyTerm p (TmxSucc t) = parensIf (p > 10) $ "succ" <+> prettyTerm 11 t
prettyTerm p (TmxNatCase t tz x ts) =
  parensIf (p > 0)
  $ vsep
  [ nest 2
    $ vsep
      [ "case" <+> pretty t <+> "of"
      , "| 0 ->" <+> pretty tz
      , "| succ" <+> pretty x <+> "->" <+> pretty ts
      ]
  , "end"
  ]
prettyTerm p (TmxBinOp bop t0 t1) = parensIf (p > p') . hang 2 $ align (prettyTerm lp t0) <+> pretty bop <+> align (prettyTerm rp t1)
  where
    (p', lp, rp) = precedenceBinOp bop
prettyTerm p (TmxBox t) = parensIf (p > 10) . hang 2 $ "box" <> softline <> group (prettyTerm 11 t)
prettyTerm p (TmxLetBox x t t0) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest 2
      $ fillSep
        [ "let box" <+> pretty x <+> "="
        , pretty t
        ]
    , "in" <+> pretty t0
    ]
prettyTerm p (TmxLam x mayTy t) =
  parensIf (p > 0)
  . align
  . nest 2
  $ fillSep
    [ "fun" <+> prettyParams params <+> "->"
    , group $ pretty t
    ]
  where
    params = (x, mayTy) : getParams t

    getParams (TmxLam x' mayTy' t') = (x', mayTy') : getParams t'
    getParams _                     = []
prettyTerm p (TmxApp t0 t1) =
  parensIf (p > 10)
  . nest 2
  $ fillSep
    [ prettyTerm 10 t0
    , prettyTerm 11 t1
    ]
prettyTerm p (TmxAnn t ty) =
  parensIf (p > 0)
  . nest 2
  $ fillSep
    [ prettyTerm 1 t
    , colon <+> prettyType 0 ty
    ]

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  d = parens d
parensIf False d = d

prettyParam :: (ElId, Maybe ElxType) -> Doc ann
prettyParam (x, Just ty) = parens (pretty x <+> colon <+> pretty ty)
prettyParam (x, Nothing) = pretty x

prettyParams :: [(ElId, Maybe ElxType)] -> Doc ann
prettyParams = vsep . fmap prettyParam
