{-# LANGUAGE DeriveAnyClass    #-}
module Elevator.ExampleModes.InfoFlowModes where

import Data.Hashable
import Elevator.ModeSpec
import GHC.Generics

data InfoFlowModes = MCode | MProg | MSecure
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec InfoFlowModes where
  showMode MCode = "C"
  showMode MProg = "P"
  showMode MSecure = "S"

  readModeEither "C" = Right MCode
  readModeEither "P" = Right MProg
  readModeEither "S" = Right MSecure
  readModeEither _   = Left "Should be either <C>, <P>, or <S>"

  MProg   <=!! MCode = True
  MSecure <=!! MCode = True
  MSecure <=!! MProg = True
  m       <=!! n     = m == n

  modeSig _  _ = True

  modeEff _ = Nothing
