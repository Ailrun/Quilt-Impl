{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Elevator.PrettyPrinter where

import Data.String       (IsString (fromString))
import Elevator.ModeSpec
import Elevator.Syntax
import Prettyprinter

instance Pretty ElId where
  pretty = viaShow

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

instance (ElModeSpec m) => Pretty (ElType m) where
  pretty = prettyType 0

prettyType :: (ElModeSpec m) => Int -> ElType m -> Doc ann
prettyType _ TyNat = "Nat"
prettyType _ TyBool = "Bool"
prettyType p (TyUp l m ty) = parensIf (p > 1) $ "Up" <+> prettyMode l <+> "=>" <+> prettyMode m <+> prettyType 2 ty
prettyType p (TyDown h m ty) = parensIf (p > 1) $ "Down" <+> prettyMode h <+> "=>" <+> prettyMode m <+> prettyType 2 ty
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
prettyTerm _ (TmNat n) = pretty n
prettyTerm p (TmSucc t) = parensIf (p > 10) $ "succ" <+> prettyTerm 11 t
prettyTerm p (TmNatCase t tz x ts) =
  parensIf (p > 0)
  $ vsep
  [ nest 2
    $ vsep
      [ "case" <+> pretty t <+> "of"
      , "0 ->" <+> pretty tz
      , "succ" <+> pretty x <+> "->" <+> pretty ts
      ]
  , "end"
  ]
prettyTerm p (TmBinOp bop t0 t1) = parensIf (p > p') $ prettyTerm lp t0 <+> pretty bop <+> prettyTerm rp t1
  where
    (p', lp, rp) = precedenceBinOp bop
prettyTerm p (TmLift m t) = parensIf (p > 10) $ "lift" <+> prettyMode m <+> prettyTerm 11 t
prettyTerm p (TmUnlift m t) = parensIf (p > 10) $ "unlift" <+> prettyMode m <+> prettyTerm 11 t
prettyTerm p (TmRet m t) = parensIf (p > 10) $ "return" <+> prettyMode m <+> prettyTerm 11 t
prettyTerm p (TmLetRet m x t t0) =
  parensIf (p > 0)
  . align
  $ vsep
    [ nest 2
      $ vsep
        [ "let return" <+> prettyMode m <+> pretty x <+> "="
        , pretty t
        ]
    , "in" <+> pretty t0
    ]
prettyTerm p (TmLam x mayTy t) =
  parensIf (p > 0)
  . nest 2
  $ vsep
    [ "fun" <+> prettyParams params <+> "->"
    , pretty t
    ]
  where
    params = (x, mayTy) : getParams t

    getParams (TmLam x' mayTy' t') = (x', mayTy') : getParams t'
    getParams _                    = []
prettyTerm p (TmApp t0 t1) =
  parensIf (p > 10)
  . nest 2
  $ vsep
    [ prettyTerm 10 t0
    , prettyTerm 11 t1
    ]

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  d = parens d
parensIf False d = d

prettyParam :: (ElModeSpec m) => (ElId, Maybe (ElType m)) -> Doc ann
prettyParam (x, Just ty) = parens (pretty x <+> colon <+> pretty ty)
prettyParam (x, Nothing) = pretty x

prettyParams :: (ElModeSpec m) => [(ElId, Maybe (ElType m))] -> Doc ann
prettyParams = vsep . fmap prettyParam

prettyMode :: (ElModeSpec m) => m -> Doc ann
prettyMode = angles . fromString . showMode

precedenceBinOp :: ElBinOp -> (Int, Int, Int)
precedenceBinOp OpAdd = (4, 4, 5)
precedenceBinOp OpSub = (4, 4, 5)
precedenceBinOp OpMul = (5, 5, 6)
precedenceBinOp OpDiv = (5, 5, 6)
precedenceBinOp OpMod = (5, 5, 6)
precedenceBinOp OpEq = (2, 3, 3)
precedenceBinOp OpNe = (2, 3, 3)
precedenceBinOp OpLe = (2, 3, 3)
precedenceBinOp OpLt = (2, 3, 3)
precedenceBinOp OpGe = (2, 3, 3)
precedenceBinOp OpGt = (2, 3, 3)
