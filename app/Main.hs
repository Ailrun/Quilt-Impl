module Main where

import Data.Text.IO         qualified as T
import Elevator.ModeSpec    (ElModeSpec (..), ElMdSt (..), ElMdOp (..))
import Elevator.Parser      (fullParse)
import Elevator.TypeChecker (typeInfer)
import System.IO            (hFlush, stdout)
import qualified Data.Set as Set

data TwoMode = MCode | MProg
  deriving (Eq, Show)

instance ElModeSpec TwoMode where
  msshow MCode = "c"
  msshow MProg = "p"

  msreadMay "c" = Just MCode
  msreadMay "p" = Just MProg
  msreadMay _   = Nothing

  MProg <=!! MCode = True
  m     <=!! n     = m == n

  msst MProg = MdStAll
  msst MCode = MdStAll

  msop MProg = Set.fromList [MdOpNat, MdOpBool, MdOpArr, MdOpDown]
  msop MCode = Set.fromList [MdOpNat, MdOpBool, MdOpArr, MdOpUp]

main :: IO ()
main = do
  putStr "> "
  hFlush stdout
  l <- T.getLine
  case helper l of
    Right (tm, ty) -> do
      putStrLn "The type of"
      putStrLn $ "  " <> show tm
      putStrLn "is"
      putStrLn $ "  " <> show ty
    Left err -> putStrLn $ "Error: " <> err
  main
  where
    helper l = do
      tm <- fullParse "<line>" l
      (,) tm <$> typeInfer MProg tm
