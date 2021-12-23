{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TupleSections #-}

-- | Adds cost-centers to call sites selected with the @-fprof-caller=...@
-- flag.
module GHC.Core.LateCC
    ( addLateCostCentres
    ) where

import Data.Word (Word8)

import Control.Applicative
import GHC.Utils.Monad.State.Strict
import Control.Monad

import GHC.Prelude
import GHC.Utils.Outputable as Outputable
import GHC.Driver.Session
import GHC.Types.CostCentre
import GHC.Types.CostCentre.State
import GHC.Types.Name hiding (varName)
import GHC.Types.Tickish
import GHC.Unit.Module.ModGuts
import GHC.Types.Var
import GHC.Unit.Types
import GHC.Data.FastString
import GHC.Core
import GHC.Core.Opt.Monad
import GHC.Utils.Panic
import qualified GHC.Utils.Binary as B
import GHC.Types.Id
import GHC.Core.Stats (exprSize)
import GHC.Utils.Trace (pprTraceM)
import GHC.Core.Utils (mkTick)

addLateCostCentres :: ModGuts -> CoreM ModGuts
addLateCostCentres guts = do
  pprTraceM "LateCC" (ppr $ mg_module guts)
  dflags <- getDynFlags
  let env :: Env
      env = Env
        { thisModule = mg_module guts
        , ccState = newCostCentreState
        , dflags = dflags
        , revParents = []
        }
  let guts' = guts { mg_binds = doCoreProgram env (mg_binds guts)
                   }
  return guts'

doCoreProgram :: Env -> CoreProgram -> CoreProgram
doCoreProgram env binds = flip evalState newCostCentreState $ do
    mapM (doBind env) binds

doBind :: Env -> CoreBind -> M CoreBind
doBind env (NonRec b rhs) = NonRec b <$> doBndr env b rhs
doBind env (Rec bs) = Rec <$> mapM doPair bs
  where
    doPair :: ((Id, CoreExpr) -> M (Id, CoreExpr))
    doPair (b,rhs) = (b,) <$> doBndr env b rhs

doBndr :: Env -> Id -> CoreExpr -> M CoreExpr
doBndr env bndr rhs = do
    pprTraceM "doBndr" (ppr bndr)
    let name = idName bndr
        name_loc = nameSrcSpan name
        cc_name = getOccFS name
        count = gopt Opt_ProfCountEntries (dflags env)
    cc_flavour <- (getCCExprFlavour cc_name) -- (ccState env)
    let cc_mod = thisModule env
        bndrCC = NormalCC cc_flavour cc_name cc_mod name_loc
        note = ProfNote bndrCC count True
    return $ mkTick note rhs

type M = State CostCentreState

getCCExprFlavour :: FastString -> M CCFlavour
getCCExprFlavour name = ExprCC <$> getCCIndex' name

getCCIndex' :: FastString -> M CostCentreIndex
getCCIndex' name = state (getCCIndex name)

data Env = Env
  { thisModule  :: Module
  , dflags      :: DynFlags
  , ccState     :: CostCentreState
  , revParents  :: [Id] -- Functions we are inside of.
  }

addParent :: Id -> Env -> Env
addParent i env = env { revParents = i : revParents env }

parents :: Env -> [Id]
parents env = reverse (revParents env)


data NamePattern
    = PChar Char NamePattern
    | PWildcard NamePattern
    | PEnd

instance Outputable NamePattern where
  ppr (PChar c rest) = char c <> ppr rest
  ppr (PWildcard rest) = char '*' <> ppr rest
  ppr PEnd = Outputable.empty

instance B.Binary NamePattern where
  get bh = do
    tag <- B.get bh
    case tag :: Word8 of
      0 -> PChar <$> B.get bh <*> B.get bh
      1 -> PWildcard <$> B.get bh
      2 -> pure PEnd
      _ -> panic "Binary(NamePattern): Invalid tag"
  put_ bh (PChar x y) = B.put_ bh (0 :: Word8) >> B.put_ bh x >> B.put_ bh y
  put_ bh (PWildcard x) = B.put_ bh (1 :: Word8) >> B.put_ bh x
  put_ bh PEnd = B.put_ bh (2 :: Word8)
