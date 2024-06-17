{-# LANGUAGE DeriveAnyClass    #-}
module Elevator.ExampleModes.PrivacyModes where

import Data.Hashable
import Elevator.ModeSpec
import GHC.Generics

data PrivacyModes = MCode | MProg | MSecure
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec PrivacyModes where
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

  modePolyTime _ = False
