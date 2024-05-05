{-# LANGUAGE DeriveAnyClass    #-}
module Elevator.ExampleModes.TwoModes where

import Data.Hashable
import Elevator.ModeSpec
import GHC.Generics

data TwoMode = MCode | MProg
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec TwoMode where
  showMode MCode = "C"
  showMode MProg = "P"

  readModeEither "C" = Right MCode
  readModeEither "P" = Right MProg
  readModeEither _   = Left "Should be either <C> or <P>"

  MProg <=!! MCode = True
  m     <=!! n     = m == n

  modeSt MProg _ = True
  modeSt MCode _ = True

  modePolyTime _ = False

-- Example Program
-- > ITmApp (ITmLam (IPatVar "x") (ITyInt MProg) (ITmVar "x")) (ITmLam (IPatVar "x") (ITyInt MProg) (ITmVar "x"))
