module Elevator.Evaluator where

import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.List           (foldl')
import Elevator.ModeSpec
import Elevator.Syntax
import GHC.Natural (Natural)
import Control.Applicative (liftA3, Applicative (liftA2))

newtype ElEnv m = ElEnv (HashMap ElId (Either m (ElEnv m, ElTerm m, m)))
  deriving Show

eval :: (ElModeSpec m) => ElProgram m -> m -> ElTerm m -> Either String (ElTerm m)
eval (ElProgram tops) = evalImpl . ElEnv $ foldl' helper HashMap.empty tops
  where
    helper envMap (ElDef x m _ t) = HashMap.insert x (Right (ElEnv envMap, t, m)) envMap

evalImpl :: (ElModeSpec m) => ElEnv m -> m -> ElTerm m -> Either String (ElTerm m)
evalImpl (ElEnv envMap) m (TmVar x) =
    case HashMap.lookup x envMap of
      Just (Left m') 
        | m == m'   -> pure $ TmVar x
      Just (Right (env', t, m'))
        | m == m'   -> evalImpl env' m t
      Just a        -> Left $ "Variable \"" <> show x <> "\"" <> " is not in mode <" <> show m <> "> " <> show a
      Nothing       -> Left $ "Variable \"" <> show x <> "\"" <> " has no reference"
evalImpl _ _ TmTrue = pure TmTrue
evalImpl _ _ TmFalse = pure TmFalse
evalImpl env m (TmIte t t0 t1) = do
  r <- evalImpl env m t
  case r of
    TmTrue  -> evalImpl env m t0
    TmFalse -> evalImpl env m t1
    _       -> Left $ "Non boolean result from the condition \"" <> show r <> "\""
evalImpl _ _ (TmNat n) = pure $ TmNat n
evalImpl env m (TmSucc t) = do
  r <- evalImpl env m t
  case r of
    TmNat n -> pure $ TmNat (1 + n)
    _       -> Left $ "Non natural number result for the operand \"" <> show r <> "\" of succ"
evalImpl env m (TmNatCase t tz x ts) = do
  r <- evalImpl env m t
  case r of
    TmNat 0 -> evalImpl env m tz
    TmNat n -> evalImpl (envInsert x m (TmNat (n - 1)) env) m ts
    _       -> Left $ "Non natural number result for the scrutinee \"" <> show r <> "\""
evalImpl env m (TmBinOp bop t0 t1) = do
  r0 <- evalImpl env m t0
  r1 <- evalImpl env m t1
  case (r0, r1) of
    (TmNat n0, TmNat n1) -> pure $ computeBop bop n0 n1
    (TmNat _, _)         -> Left $ "Non natural number result for the second operand \"" <> show r1 <> "\""
    (_, _)               -> Left $ "Non natural number result for the first operands \"" <> show r0 <> "\""
evalImpl env m (TmLift l t) = do
  r <- canonEvalImpl env m l t
  pure $ TmLift l r
evalImpl env m (TmUnlift h t) = do
  r <- evalImpl env h t
  case r of
    TmLift m' t'
      | m == m'   -> evalImpl env m t'
      | otherwise -> Left $ "Deferred expression has different mode \"" <> show m' <> "\" from the executing mode \"" <> show m <> "\""
    _             -> Left $ "Non deferred expression result \"" <> show r <> "\" for unlift"
evalImpl env _ (TmRet h t) = TmRet h <$> evalImpl env h t
evalImpl env m (TmLetRet h x t t0) = do
  r <- evalImpl env m t
  case r of
    TmRet h' t'
      | h == h'   -> evalImpl (envInsert x h t' env) m t0
      | otherwise -> Left $ "Stored value has different mode \"" <> show h' <> "\" from the loading mode \"" <> show h <> "\""
    _             -> Left $ "Non pointer result \"" <> show r <> "\" for let return"
evalImpl _ _ (TmLam x ty t) = pure $ TmLam x ty t
evalImpl env m (TmApp t0 t1) = do
  r0 <- evalImpl env m t0
  r1 <- evalImpl env m t1
  case r0 of
    TmLam x _ t -> evalImpl (envInsert x m r1 env) m t
    _           -> Left $ "Non function result \"" <> show r0 <> "\" for application"

canonEvalImpl :: (ElModeSpec m) => ElEnv m -> m -> m -> ElTerm m -> Either String (ElTerm m)
canonEvalImpl _ _ _ (TmVar x) = pure $ TmVar x
canonEvalImpl _ _ _ TmTrue = pure TmTrue
canonEvalImpl _ _ _ TmFalse = pure TmFalse
canonEvalImpl env h m (TmIte t t0 t1) =
  liftA3
    TmIte
    (canonEvalImpl env h m t)
    (canonEvalImpl env h m t0)
    (canonEvalImpl env h m t1)
canonEvalImpl _ _ _ (TmNat n) = pure $ TmNat n
canonEvalImpl env h m (TmSucc t) = TmSucc <$> canonEvalImpl env h m t
canonEvalImpl env h m (TmNatCase t tz x ts) = do
  liftA3
    (\c cz cs -> TmNatCase c cz x cs)
    (canonEvalImpl env h m t)
    (canonEvalImpl env h m tz)
    (canonEvalImpl env h m ts)
canonEvalImpl env h m (TmBinOp bop t0 t1) = do
  liftA2
    (TmBinOp bop)
    (canonEvalImpl env h m t0)
    (canonEvalImpl env h m t1)
canonEvalImpl env h _ (TmLift l t) = TmLift l <$> canonEvalImpl env h l t
canonEvalImpl env h m (TmUnlift h' t)
  | h' >=!! h = do
    r <- evalImpl env h' t
    case r of
      TmLift m' t'
        | m == m'   -> pure t'
        | otherwise -> Left $ "Deferred expression has different mode \"" <> show m' <> "\" from the executing mode \"" <> show m <> "\""
      _             -> Left $ "Non deferred expression result \"" <> show r <> "\" for unlift"
  | otherwise = TmUnlift h' <$> canonEvalImpl env h h' t
canonEvalImpl env h _ (TmRet h' t)
  | h' >=!! h = TmRet h' <$> evalImpl env h' t
  | otherwise = TmRet h' <$> canonEvalImpl env h h' t
canonEvalImpl env h m (TmLetRet h' x t t0) = do
  liftA2
    (TmLetRet h' x)
    (canonEvalImpl env h m t)
    (canonEvalImpl (envEmptyInsert x h' env) h m t0)
canonEvalImpl env h m (TmLam x ty t) = TmLam x ty <$> canonEvalImpl env h m t
canonEvalImpl env h m (TmApp t0 t1) =
  liftA2
    TmApp
    (canonEvalImpl env h m t0)
    (canonEvalImpl env h m t1)

computeBop :: ElBinOp -> Natural -> Natural -> ElTerm m
computeBop OpAdd n0 n1 = TmNat (n0 + n1)
computeBop OpSub n0 n1
  | n0 >= n1  = TmNat (n0 - n1)
  | otherwise = TmNat 0
computeBop OpMul n0 n1 = TmNat (n0 * n1)
computeBop OpDiv n0 n1 = TmNat (n0 `div` n1)
computeBop OpMod n0 n1 = TmNat (n0 `mod` n1)
computeBop OpEq n0 n1
  | n0 == n1  = TmTrue
  | otherwise = TmFalse
computeBop OpNe n0 n1
  | n0 /= n1  = TmTrue
  | otherwise = TmFalse
computeBop OpLe n0 n1
  | n0 <= n1  = TmTrue
  | otherwise = TmFalse
computeBop OpLt n0 n1
  | n0 < n1   = TmTrue
  | otherwise = TmFalse
computeBop OpGe n0 n1
  | n0 >= n1  = TmTrue
  | otherwise = TmFalse
computeBop OpGt n0 n1
  | n0 > n1   = TmTrue
  | otherwise = TmFalse

envInsert :: ElId -> m -> ElTerm m -> ElEnv m -> ElEnv m
envInsert x m t env@(ElEnv envMap) = ElEnv (HashMap.insert x (Right (env, t, m)) envMap)

envEmptyInsert :: ElId -> m -> ElEnv m -> ElEnv m
envEmptyInsert x m (ElEnv envMap) = ElEnv (HashMap.insert x (Left m) envMap)
