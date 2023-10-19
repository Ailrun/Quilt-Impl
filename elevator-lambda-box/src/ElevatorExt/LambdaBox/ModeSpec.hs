{-# LANGUAGE DeriveAnyClass #-}
module ElevatorExt.LambdaBox.ModeSpec where

import           Data.Hashable     (Hashable)
import           Elevator.ModeSpec (ElModeSpec (..))
import           GHC.Generics      (Generic)

data Mode = MCode | MProg
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec Mode where
  showMode MCode = "c"
  showMode MProg = "p"

  readModeEither "c" = Right MCode
  readModeEither "p" = Right MProg
  readModeEither _   = Left "Should be either c or p"

  MProg <=!! MCode = True
  m     <=!! n     = m == n

  modeSt MProg _ = True
  modeSt MCode _ = True

  modeOp MProg _ = True
  modeOp MCode _ = True

