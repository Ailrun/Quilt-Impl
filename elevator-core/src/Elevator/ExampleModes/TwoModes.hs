{-# LANGUAGE DeriveAnyClass    #-}
module Elevator.ExampleModes.TwoModes where

import Data.Hashable
import Elevator.ModeSpec
import GHC.Generics

data TwoModes = MCode | MProg
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec TwoModes where
  showMode MCode = "C"
  showMode MProg = "P"

  readModeEither "C" = Right MCode
  readModeEither "P" = Right MProg
  readModeEither _   = Left "Should be either <C> or <P>"

  MProg <=!! MCode = True
  m     <=!! n     = m == n

  modeSig _ _ = True

  modeEff _ = Nothing

-- Example Program
-- > ITmApp (ITmLam (IPatVar "x") (ITyArr (ITyInt MProg) (ITyInt MProg)) (ITmVar "x")) (ITmLam (IPatVar "x") (ITyInt MProg) (ITmVar "x"))
-- > ITmApp (ITmApp (ITmApp (ITmLam (IPatVar "x") (ITyInt MProg) (ITmLam (IPatVar "y") (ITyUp MCode [("x",MProg,ICEType (ITyInt MProg))] (ITyInt MProg)) (ITmForce MCode (ITmVar "y") [ISETerm (ITmVar "x")]))) (ITmInt 3)) (ITmSusp MCode [("x",MProg,False)] (ITmLam (IPatVar "z") (ITyInt MProg) (ITmBinOp OpAdd (ITmVar "x") (ITmVar "z"))))) (ITmInt 12)
