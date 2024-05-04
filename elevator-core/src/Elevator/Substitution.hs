{-# LANGUAGE DerivingStrategies #-}
module Elevator.Substitution where

import Control.Monad.Except       (ExceptT, MonadError (..))
import Control.Monad.State.Strict (MonadState (..), State)
import Data.String                (IsString (fromString))
import Elevator.ModeSpec
import Elevator.Syntax
import qualified Data.Sequence as Seq
import Data.Traversable.Compat (mapAccumM)
import Data.Tuple (swap)

------------------------------------------------------------
-- These uses @ElContextHat@ instead of @ElIContextHat@, as
-- we don't need modes of variables.
------------------------------------------------------------

applySubstKind :: (ElModeSpec m) => ElISubst m -> ElContextHat m -> ElIKind m -> ElSubstM (ElIKind m)
applySubstKind = _

applySubstCtx :: (ElModeSpec m) => ElISubst m -> ElContextHat m -> ElIContext m -> ElSubstM (ElIContext m)
applySubstCtx = _

applySubstType :: (ElModeSpec m) => ElISubst m -> ElContextHat m -> ElIType m -> ElSubstM (ElIType m)
applySubstType = _

applySubstTerm :: (ElModeSpec m) => ElISubst m -> ElContextHat m -> ElITerm m -> ElSubstM (ElITerm m)
applySubstTerm _ _ (ITmVar x) = _

freshTmVarInTerm :: (ElModeSpec m) => ElId -> ElITerm m -> ElSubstM (ElId, ElITerm m)
freshTmVarInTerm x tm = do
  x' <- freshOf x
  (x',) <$> applySubstTerm (Seq.singleton (ISETerm (ITmVar x))) (Seq.singleton x') tm

freshTmVarsInTerm :: (ElModeSpec m) => [ElId] -> ElITerm m -> ElSubstM ([ElId], ElITerm m)
freshTmVarsInTerm xs tm = swap <$> mapAccumM ((fmap swap .) . flip freshTmVarInTerm) tm xs

freshTyVarInTerm :: (ElModeSpec m) => ElId -> ElITerm m -> ElSubstM (ElId, ElITerm m)
freshTyVarInTerm x tm = do
  x' <- freshOf x
  (x',) <$> applySubstTerm (Seq.singleton (ISEType (ITyVar x))) (Seq.singleton x') tm

freshOf :: ElId -> ElSubstM ElId
freshOf x = do
  n <- get
  put (succ n)
  pure $ x <> fromString (show n)

newtype ElSubstM a = ElSubstM { runElSubstM :: ExceptT String (State Integer) a }
  deriving newtype (Functor, Applicative, Monad, MonadError String, MonadState Integer)
