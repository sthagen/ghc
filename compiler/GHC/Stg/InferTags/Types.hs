{-# LANGUAGE TypeFamilies, DataKinds, GADTs, FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE UndecidableInstances #-}
 -- To permit: type instance XLet 'InferTaggedBinders = XLet 'Vanilla

module GHC.Stg.InferTags.Types
    ( module GHC.Stg.InferTags.Types
    , module TagSig)
where

import GHC.Prelude

import GHC.Core.DataCon
import GHC.Core.Type (isUnliftedType)
import GHC.Types.Id
import GHC.Stg.Syntax
import GHC.Stg.InferTags.TagSig as TagSig
import GHC.Types.Var.Env
import GHC.Utils.Outputable
import GHC.Utils.Misc( zipWithEqual )

import GHC.Utils.Panic
import GHC.StgToCmm.Types

{- *********************************************************************
*                                                                      *
                         Supporting data types
*                                                                      *
********************************************************************* -}

type instance BinderP      'InferTaggedBinders = (Id, TagSig)
type instance XLet         'InferTaggedBinders = XLet         'Vanilla
type instance XLetNoEscape 'InferTaggedBinders = XLetNoEscape 'Vanilla
type instance XRhsClosure  'InferTaggedBinders = XRhsClosure  'Vanilla

type InferStgTopBinding = GenStgTopBinding 'InferTaggedBinders
type InferStgBinding    = GenStgBinding    'InferTaggedBinders
type InferStgExpr       = GenStgExpr       'InferTaggedBinders
type InferStgRhs        = GenStgRhs        'InferTaggedBinders
type InferStgAlt        = GenStgAlt        'InferTaggedBinders

combineAltInfo :: TagInfo -> TagInfo -> TagInfo
combineAltInfo TagDunno         _              = TagDunno
combineAltInfo _                TagDunno       = TagDunno
combineAltInfo (TagTuple {})    TagProper      = panic "Combining unboxed tuple with non-tuple result"
combineAltInfo TagProper       (TagTuple {})   = panic "Combining unboxed tuple with non-tuple result"
combineAltInfo TagProper        TagProper      = TagProper
combineAltInfo (TagTuple is1)  (TagTuple is2)  = TagTuple (zipWithEqual "combineAltInfo" combineAltInfo is1 is2)
combineAltInfo (TagTagged)      ti             = ti
combineAltInfo ti               TagTagged      = ti

type TagSigEnv = IdEnv TagSig
data TagEnv p = TE { te_env :: TagSigEnv
                   , te_get :: BinderP p -> Id
                   }

instance Outputable (TagEnv p) where
    ppr te = ppr (te_env te)


getBinderId :: TagEnv p -> BinderP p -> Id
getBinderId = te_get

initEnv :: TagEnv 'Vanilla
initEnv = TE { te_env = emptyVarEnv
             , te_get = \x -> x}

-- | Simple convert env to a env of the 'InferTaggedBinders pass
-- with no other changes.
makeTagged :: TagEnv p -> TagEnv 'InferTaggedBinders
makeTagged env = TE { te_env = te_env env
                    , te_get = fst }

noSig :: TagEnv p -> BinderP p -> (Id, TagSig)
noSig env bndr
  | isUnliftedType (idType var) = (var, TagSig TagProper)
  | otherwise = (var, TagSig TagDunno)
  where
    var = getBinderId env bndr

lookupSig :: TagEnv p -> Id -> Maybe TagSig
lookupSig env fun = lookupVarEnv (te_env env) fun

lookupInfo :: TagEnv p -> StgArg -> TagInfo
lookupInfo env (StgVarArg var)
  -- Nullary data constructors like True, False
  | Just dc <- isDataConWorkId_maybe var
  , isNullaryRepDataCon dc
  = TagProper

  | isUnliftedType (idType var)
  = TagProper

  -- Variables in the environment.
  | Just (TagSig info) <- lookupVarEnv (te_env env) var
  = info

  | Just lf_info <- idLFInfo_maybe var
  =   case lf_info of
          -- Function, tagged (with arity)
          LFReEntrant {}
              -> TagProper
          -- Thunks need to be entered.
          LFThunk {}
              -> TagDunno
          -- Constructors, already tagged.
          LFCon {}
              -> TagProper
          LFUnknown {}
              -> TagDunno
          LFUnlifted {}
              -> TagProper
          -- Shouldn't be possible. I don't think we can export letNoEscapes
          LFLetNoEscape {} -> panic "LFLetNoEscape exported"

  | otherwise
  = TagDunno

lookupInfo _ (StgLitArg {})
  = TagProper

isDunnoSig :: TagSig -> Bool
isDunnoSig (TagSig TagDunno) = True
isDunnoSig (TagSig TagProper) = False
isDunnoSig (TagSig TagTuple{}) = False
isDunnoSig (TagSig TagTagged{}) = False

isTaggedInfo :: TagInfo -> Bool
isTaggedInfo TagProper = True
isTaggedInfo TagTagged = True
isTaggedInfo _         = False

extendSigEnv :: TagEnv p -> [(Id,TagSig)] -> TagEnv p
extendSigEnv env@(TE { te_env = sig_env }) bndrs
  = env { te_env = extendVarEnvList sig_env bndrs }
