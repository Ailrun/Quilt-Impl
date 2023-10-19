{-# LANGUAGE DeriveAnyClass #-}
module ElevatorExt.LambdaBox.ModeSpec where

import           Data.Hashable     (Hashable)
import           Elevator.ModeSpec (ElModeSpec (..))
import           GHC.Generics      (Generic)

data Mode = MUnre | MLine
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec Mode where
  showMode MUnre = "c"
  showMode MLine = "p"

  readModeEither "c" = Right MUnre
  readModeEither "p" = Right MLine
  readModeEither _   = Left "Should be either c or p"

  MLine <=!! MUnre = True
  m     <=!! n     = m == n

  modeSt MLine _ = True
  modeSt MUnre _ = True

  modeOp MLine _ = True
  modeOp MUnre _ = True

