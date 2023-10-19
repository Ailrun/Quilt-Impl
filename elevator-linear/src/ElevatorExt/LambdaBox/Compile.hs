module ElevatorExt.LambdaBox.Compile where

import           Data.HashMap.Strict            (HashMap)
import qualified Data.HashMap.Strict            as HashMap
import           Elevator.Syntax                (ElITerm (..), ElId,
                                                 ElProgram (..), ElTerm (..),
                                                 ElTop (..), ElType (..))
import           ElevatorExt.LambdaBox.ModeSpec (Mode (..))
import           ElevatorExt.LambdaBox.Syntax   (ElxProgram (..), ElxTerm (..),
                                                 ElxTop (..), ElxType (..))

type Globalness = Bool

compileType :: ElxType -> ElType Mode
compileType TyxNat = TyNat
compileType TyxBool = TyBool
compileType (TyxBox tyx) = TyDown MCode MProg . TyUp MProg MCode $ compileType tyx
compileType (TyxArr tyx0 tyx1) = TyArr (compileType tyx0) (compileType tyx1)

compileProg :: ElxProgram -> ElProgram Mode
compileProg (ElxProgram topxs) = ElProgram $ compileTop <$> topxs

compileTop :: ElxTop -> ElTop Mode
compileTop (ElxDef x ty tm) = ElDef x MProg (compileType ty) (compileTerm tm)

compileTerm :: ElxTerm -> ElTerm Mode
compileTerm = compileTermImpl HashMap.empty

compileTermImpl :: HashMap ElId Globalness -> ElxTerm -> ElTerm Mode
compileTermImpl ctx (TmxVar x)
  | Just True <- HashMap.lookup x ctx = TmUnlift MCode (TmVar x)
  | otherwise                         = TmVar x
compileTermImpl _ TmxTrue = TmTrue
compileTermImpl _ TmxFalse = TmFalse
compileTermImpl ctx (TmxIte tx tx0 tx1) = TmIte (compileTermImpl ctx tx) (compileTermImpl ctx tx0) (compileTermImpl ctx tx1)
compileTermImpl _ (TmxNat n) = TmNat n
compileTermImpl ctx (TmxSucc tx) = TmSucc $ compileTermImpl ctx tx
compileTermImpl ctx (TmxNatCase tx txz x txs) = TmNatCase (compileTermImpl ctx tx) (compileTermImpl ctx txz) x (compileTermImpl (HashMap.insert x False ctx) txs)
compileTermImpl ctx (TmxBinOp bop tx0 tx1) = TmBinOp bop (compileTermImpl ctx tx0) (compileTermImpl ctx tx1)
compileTermImpl ctx (TmxBox tx) = TmRet (Just MCode) . TmLift (Just MProg) $ compileTermImpl (HashMap.filter id ctx) tx
compileTermImpl ctx (TmxLetBox x tx tx0) = TmLetRet (Just MCode) x (compileTermImpl ctx tx) (compileTermImpl (HashMap.insert x True ctx) tx0)
compileTermImpl ctx (TmxLam x mayTyx tx) = TmLam x (compileType <$> mayTyx) (compileTermImpl (HashMap.insert x False ctx) tx)
compileTermImpl ctx (TmxApp tx0 tx1) = TmApp (compileTermImpl ctx tx0) (compileTermImpl ctx tx1)
compileTermImpl ctx (TmxAnn tx tyx) = TmAnn (compileTermImpl ctx tx) (compileType tyx)

decompileType :: ElType Mode -> ElxType
decompileType TyNat = TyxNat
decompileType TyBool = TyxBool
decompileType (TyUp _ _ _) = error "impossible!"
decompileType (TyDown MCode MProg (TyUp MProg MCode ty)) = TyxBox $ decompileType ty
decompileType (TyDown _ _ _) = error "impossible!"
decompileType (TyArr ty0 ty1) = TyxArr (decompileType ty0) (decompileType ty1)

decompileTerm :: ElITerm Mode -> ElxTerm
decompileTerm = decompileTermImpl HashMap.empty

decompileTermImpl :: HashMap ElId Globalness -> ElITerm Mode -> ElxTerm
decompileTermImpl ctx (ITmVar x)
  | Just True <- HashMap.lookup x ctx = error "Impossible!"
  | otherwise                         = TmxVar x
decompileTermImpl _ ITmTrue = TmxTrue
decompileTermImpl _ ITmFalse = TmxFalse
decompileTermImpl ctx (ITmIte it it0 it1) = TmxIte (decompileTermImpl ctx it) (decompileTermImpl ctx it0) (decompileTermImpl ctx it1)
decompileTermImpl _ (ITmNat n) = TmxNat n
decompileTermImpl ctx (ITmSucc it) = TmxSucc (decompileTermImpl ctx it)
decompileTermImpl ctx (ITmNatCase it itz x its) = TmxNatCase (decompileTermImpl ctx it) (decompileTermImpl ctx itz) x (decompileTermImpl (HashMap.insert x False ctx) its)
decompileTermImpl ctx (ITmBinOp bop it0 it1) = TmxBinOp bop (decompileTermImpl ctx it0) (decompileTermImpl ctx it1)
decompileTermImpl _ (ITmLift _ _) = error "Impossible!"
decompileTermImpl ctx (ITmUnlift MCode (ITmVar x))
  | Just True <- HashMap.lookup x ctx = TmxVar x
  | otherwise                         = error "Impossible!"
decompileTermImpl ctx (ITmUnlift MCode (ITmLift MProg it)) = decompileTermImpl (HashMap.filter id ctx) it
decompileTermImpl _ (ITmUnlift _ _) = error "Impossible!"
decompileTermImpl ctx (ITmRet MCode (ITmLift MProg it)) = TmxBox (decompileTermImpl (HashMap.filter id ctx) it)
decompileTermImpl _ (ITmRet _ _) = error "Impossible!"
decompileTermImpl ctx (ITmLetRet MCode x it it0) = TmxLetBox x (decompileTermImpl ctx it) (decompileTermImpl (HashMap.insert x True ctx) it0)
decompileTermImpl ctx (ITmLetRet _ _ _ _) = error "Impossible!"
decompileTermImpl ctx (ITmLam x ty it) = TmxLam x (Just $ decompileType ty) (decompileTermImpl (HashMap.insert x False ctx) it)
decompileTermImpl ctx (ITmApp it0 it1) = TmxApp (decompileTermImpl ctx it0) (decompileTermImpl ctx it1)
