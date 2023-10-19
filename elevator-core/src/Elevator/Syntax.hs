{-# LANGUAGE DerivingVia #-}
module Elevator.Syntax
  ( ElId
  , elId

  , ElType(..)

  , ElProgram(..)
  , ElTop(..)
  , ElTerm(..)

  , ElIProgram(..)
  , ElITop(..)
  , ElITerm(..)
  , iProgram2program
  , iTop2top
  , iTerm2term

  , ElBinOp(..)
  , elBinOpType
  , elBinOpTypeWithMode
  ) where

import Data.Hashable (Hashable)
import Data.Text     (Text)
import GHC.Natural   (Natural)
import Prettyprinter (Pretty)

newtype ElId = ElId Text
  deriving (Hashable, Eq, Ord, Show, Pretty) via Text

elId :: Text -> ElId
elId = ElId

data ElType m
  = TyNat
  | TyBool
  | TyUp m m (ElType m)
  | TyDown m m (ElType m)
  | TyArr (ElType m) (ElType m)
  deriving stock (Eq, Show)

newtype ElProgram m = ElProgram [ElTop m]
  deriving stock (Eq, Show)

data ElTop m
  = ElDef ElId m (ElType m) (ElTerm m)
  deriving stock (Eq, Show)

newtype ElIProgram m = ElIProgram [ElITop m]
  deriving stock (Eq, Show)

data ElITop m
  = ElIDef ElId m (ElType m) (ElITerm m)
  deriving stock (Eq, Show)

data ElTerm m
  = TmVar ElId
  | TmTrue
  | TmFalse
  | TmIte (ElTerm m) (ElTerm m) (ElTerm m)
  | TmNat Natural
  | TmSucc (ElTerm m)
  | TmNatCase (ElTerm m) (ElTerm m) ElId (ElTerm m)
  | TmBinOp ElBinOp (ElTerm m) (ElTerm m)
  | TmLift (Maybe m) (ElTerm m)
  | TmUnlift m (ElTerm m)
  | TmRet (Maybe m) (ElTerm m)
  | TmLetRet (Maybe m) ElId (ElTerm m) (ElTerm m)
  | TmLam ElId (Maybe (ElType m)) (ElTerm m)
  | TmApp (ElTerm m) (ElTerm m)
  | TmAnn (ElTerm m) (ElType m)
  deriving stock (Eq, Show)

data ElITerm m
  = ITmVar ElId
  | ITmTrue
  | ITmFalse
  | ITmIte (ElITerm m) (ElITerm m) (ElITerm m)
  | ITmNat Natural
  | ITmSucc (ElITerm m)
  | ITmNatCase (ElITerm m) (ElITerm m) ElId (ElITerm m)
  | ITmBinOp ElBinOp (ElITerm m) (ElITerm m)
  | ITmLift m (ElITerm m)
  | ITmUnlift m (ElITerm m)
  | ITmRet m (ElITerm m)
  | ITmLetRet m ElId (ElITerm m) (ElITerm m)
  | ITmLam ElId (ElType m) (ElITerm m)
  | ITmApp (ElITerm m) (ElITerm m)
  deriving stock (Eq, Show)

iProgram2program :: ElIProgram m -> ElProgram m
iProgram2program (ElIProgram tops) = ElProgram (iTop2top <$> tops)

iTop2top :: ElITop m -> ElTop m
iTop2top (ElIDef x m ty t) = ElDef x m ty (iTerm2term t)

iTerm2term :: ElITerm m -> ElTerm m
iTerm2term (ITmVar x) = TmVar x
iTerm2term ITmTrue = TmTrue
iTerm2term ITmFalse = TmFalse
iTerm2term (ITmIte it it0 it1) = TmIte (iTerm2term it) (iTerm2term it0) (iTerm2term it1)
iTerm2term (ITmNat n) = TmNat n
iTerm2term (ITmSucc it) = TmSucc (iTerm2term it)
iTerm2term (ITmNatCase it itz x its) = TmNatCase (iTerm2term it) (iTerm2term itz) x (iTerm2term its)
iTerm2term (ITmBinOp bop it0 it1) = TmBinOp bop (iTerm2term it0) (iTerm2term it1)
iTerm2term (ITmLift m it) = TmLift (Just m) (iTerm2term it)
iTerm2term (ITmUnlift m it) = TmUnlift m (iTerm2term it)
iTerm2term (ITmRet m it) = TmRet (Just m) (iTerm2term it)
iTerm2term (ITmLetRet m x it it0) = TmLetRet (Just m) x (iTerm2term it) (iTerm2term it0)
iTerm2term (ITmLam x ty it) = TmLam x (Just ty) (iTerm2term it)
iTerm2term (ITmApp it0 it1) = TmApp (iTerm2term it0) (iTerm2term it1)

data ElBinOp
  = OpAdd
  | OpSub
  | OpMul
  | OpDiv
  | OpMod
  | OpEq
  | OpNe
  | OpLe
  | OpLt
  | OpGe
  | OpGt
  deriving stock (Eq, Ord, Show)

elBinOpType :: ElBinOp -> (ElType m, ElType m, ElType m)
elBinOpType OpAdd = (TyNat, TyNat, TyNat)
elBinOpType OpSub = (TyNat, TyNat, TyNat)
elBinOpType OpMul = (TyNat, TyNat, TyNat)
elBinOpType OpDiv = (TyNat, TyNat, TyNat)
elBinOpType OpMod = (TyNat, TyNat, TyNat)
elBinOpType OpEq  = (TyNat, TyNat, TyBool)
elBinOpType OpNe  = (TyNat, TyNat, TyBool)
elBinOpType OpLe  = (TyNat, TyNat, TyBool)
elBinOpType OpLt  = (TyNat, TyNat, TyBool)
elBinOpType OpGe  = (TyNat, TyNat, TyBool)
elBinOpType OpGt  = (TyNat, TyNat, TyBool)

elBinOpTypeWithMode :: m -> ElBinOp -> (ElType m, ElType m, ElType m)
elBinOpTypeWithMode _ = elBinOpType
