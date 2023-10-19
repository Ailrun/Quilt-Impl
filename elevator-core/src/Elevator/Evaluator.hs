module Elevator.Evaluator where

import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.List           (foldl')
import Elevator.ModeSpec
import Elevator.Syntax
import GHC.Natural (Natural)
import Control.Applicative (liftA3, Applicative (liftA2))

newtype ElEnv m = ElEnv (HashMap ElId (Either m (ElEnv m, ElITerm m, m)))
  deriving Show

eval :: (ElModeSpec m) => ElIProgram m -> m -> ElITerm m -> Either String (ElITerm m)
eval (ElIProgram tops) = evalImpl . ElEnv $ foldl' helper HashMap.empty tops
  where
    helper envMap (ElIDef x m _ t) = HashMap.insert x (Right (ElEnv envMap, t, m)) envMap

evalImpl :: (ElModeSpec m) => ElEnv m -> m -> ElITerm m -> Either String (ElITerm m)
evalImpl (ElEnv envMap) m (ITmVar x) =
    case HashMap.lookup x envMap of
      Just (Left m') 
        | m == m'   -> pure $ ITmVar x
      Just (Right (env', t, m'))
        | m == m'   -> evalImpl env' m t
      Just a        -> Left $ "Variable \"" <> show x <> "\"" <> " is not in mode <" <> show m <> "> " <> show a
      Nothing       -> Left $ "Variable \"" <> show x <> "\"" <> " has no reference"
evalImpl _ _ ITmTrue = pure ITmTrue
evalImpl _ _ ITmFalse = pure ITmFalse
evalImpl env m (ITmIte t t0 t1) = do
  r <- evalImpl env m t
  case r of
    ITmTrue  -> evalImpl env m t0
    ITmFalse -> evalImpl env m t1
    _       -> Left $ "Non boolean result from the condition \"" <> show r <> "\""
evalImpl _ _ (ITmNat n) = pure $ ITmNat n
evalImpl env m (ITmSucc t) = do
  r <- evalImpl env m t
  case r of
    ITmNat n -> pure $ ITmNat (1 + n)
    _       -> Left $ "Non natural number result for the operand \"" <> show r <> "\" of succ"
evalImpl env m (ITmNatCase t tz x ts) = do
  r <- evalImpl env m t
  case r of
    ITmNat 0 -> evalImpl env m tz
    ITmNat n -> evalImpl (envInsert x m (ITmNat (n - 1)) env) m ts
    _       -> Left $ "Non natural number result for the scrutinee \"" <> show r <> "\""
evalImpl env m (ITmBinOp bop t0 t1) = do
  r0 <- evalImpl env m t0
  r1 <- evalImpl env m t1
  case (r0, r1) of
    (ITmNat n0, ITmNat n1) -> pure $ computeBop bop n0 n1
    (ITmNat _, _)         -> Left $ "Non natural number result for the second operand \"" <> show r1 <> "\""
    (_, _)               -> Left $ "Non natural number result for the first operands \"" <> show r0 <> "\""
evalImpl env m (ITmLift l t) = do
  r <- canonEvalImpl env m l t
  pure $ ITmLift l r
evalImpl env m (ITmUnlift h t) = do
  r <- evalImpl env h t
  case r of
    ITmLift m' t'
      | m == m'   -> evalImpl env m t'
      | otherwise -> Left $ "Deferred expression has different mode \"" <> show m' <> "\" from the executing mode \"" <> show m <> "\""
    _             -> Left $ "Non deferred expression result \"" <> show r <> "\" for unlift"
evalImpl env _ (ITmRet h t) = ITmRet h <$> evalImpl env h t
evalImpl env m (ITmLetRet h x t t0) = do
  r <- evalImpl env m t
  case r of
    ITmRet h' t'
      | h == h'   -> evalImpl (envInsert x h t' env) m t0
      | otherwise -> Left $ "Stored value has different mode \"" <> show h' <> "\" from the loading mode \"" <> show h <> "\""
    _             -> Left $ "Non pointer result \"" <> show r <> "\" for let return"
evalImpl _ _ (ITmLam x ty t) = pure $ ITmLam x ty t
evalImpl env m (ITmApp t0 t1) = do
  r0 <- evalImpl env m t0
  r1 <- evalImpl env m t1
  case r0 of
    ITmLam x _ t -> evalImpl (envInsert x m r1 env) m t
    _           -> Left $ "Non function result \"" <> show r0 <> "\" for application"

canonEvalImpl :: (ElModeSpec m) => ElEnv m -> m -> m -> ElITerm m -> Either String (ElITerm m)
canonEvalImpl _ _ _ (ITmVar x) = pure $ ITmVar x
canonEvalImpl _ _ _ ITmTrue = pure ITmTrue
canonEvalImpl _ _ _ ITmFalse = pure ITmFalse
canonEvalImpl env h m (ITmIte t t0 t1) =
  liftA3
    ITmIte
    (canonEvalImpl env h m t)
    (canonEvalImpl env h m t0)
    (canonEvalImpl env h m t1)
canonEvalImpl _ _ _ (ITmNat n) = pure $ ITmNat n
canonEvalImpl env h m (ITmSucc t) = ITmSucc <$> canonEvalImpl env h m t
canonEvalImpl env h m (ITmNatCase t tz x ts) = do
  liftA3
    (\c cz cs -> ITmNatCase c cz x cs)
    (canonEvalImpl env h m t)
    (canonEvalImpl env h m tz)
    (canonEvalImpl env h m ts)
canonEvalImpl env h m (ITmBinOp bop t0 t1) = do
  liftA2
    (ITmBinOp bop)
    (canonEvalImpl env h m t0)
    (canonEvalImpl env h m t1)
canonEvalImpl env h _ (ITmLift l t) = ITmLift l <$> canonEvalImpl env h l t
canonEvalImpl env h m (ITmUnlift h' t)
  | h' >=!! h = do
    r <- evalImpl env h' t
    case r of
      ITmLift m' t'
        | m == m'   -> pure t'
        | otherwise -> Left $ "Deferred expression has different mode \"" <> show m' <> "\" from the executing mode \"" <> show m <> "\""
      _             -> Left $ "Non deferred expression result \"" <> show r <> "\" for unlift"
  | otherwise = ITmUnlift h' <$> canonEvalImpl env h h' t
canonEvalImpl env h _ (ITmRet h' t)
  | h' >=!! h = ITmRet h' <$> evalImpl env h' t
  | otherwise = ITmRet h' <$> canonEvalImpl env h h' t
canonEvalImpl env h m (ITmLetRet h' x t t0) = do
  liftA2
    (ITmLetRet h' x)
    (canonEvalImpl env h m t)
    (canonEvalImpl (envEmptyInsert x h' env) h m t0)
canonEvalImpl env h m (ITmLam x ty t) = ITmLam x ty <$> canonEvalImpl env h m t
canonEvalImpl env h m (ITmApp t0 t1) =
  liftA2
    ITmApp
    (canonEvalImpl env h m t0)
    (canonEvalImpl env h m t1)

computeBop :: ElBinOp -> Natural -> Natural -> ElITerm m
computeBop OpAdd n0 n1 = ITmNat (n0 + n1)
computeBop OpSub n0 n1
  | n0 >= n1  = ITmNat (n0 - n1)
  | otherwise = ITmNat 0
computeBop OpMul n0 n1 = ITmNat (n0 * n1)
computeBop OpDiv n0 n1 = ITmNat (n0 `div` n1)
computeBop OpMod n0 n1 = ITmNat (n0 `mod` n1)
computeBop OpEq n0 n1
  | n0 == n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpNe n0 n1
  | n0 /= n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpLe n0 n1
  | n0 <= n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpLt n0 n1
  | n0 < n1   = ITmTrue
  | otherwise = ITmFalse
computeBop OpGe n0 n1
  | n0 >= n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpGt n0 n1
  | n0 > n1   = ITmTrue
  | otherwise = ITmFalse

envInsert :: ElId -> m -> ElITerm m -> ElEnv m -> ElEnv m
envInsert x m t env@(ElEnv envMap) = ElEnv (HashMap.insert x (Right (env, t, m)) envMap)

envEmptyInsert :: ElId -> m -> ElEnv m -> ElEnv m
envEmptyInsert x m (ElEnv envMap) = ElEnv (HashMap.insert x (Left m) envMap)
