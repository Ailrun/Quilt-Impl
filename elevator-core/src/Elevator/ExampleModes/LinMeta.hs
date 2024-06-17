{-# LANGUAGE DeriveAnyClass    #-}
module Elevator.ExampleModes.LinMeta where

import Data.Hashable
import Elevator.ModeSpec
import GHC.Generics

data LinMeta = MCode | MGC | MGF
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec LinMeta where
  showMode MCode = "C"
  showMode MGC = "GC"
  showMode MGF = "GF"

  readModeEither "C" = Right MCode
  readModeEither "GC" = Right MGC
  readModeEither "GF" = Right MGF
  readModeEither _   = Left "Should be either <C>, <GC>, or <GF>"

  MGC <=!! MC  = True
  MGF <=!! MC  = True
  MGF <=!! MGC = True
  m   <=!! n   = m == n

  modeSig GF _ = False
  modeSig _  _ = True

  modePolyTime _ = False
