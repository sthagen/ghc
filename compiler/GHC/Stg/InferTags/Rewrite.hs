--
-- Copyright (c) 2019 Andreas Klebinger
--

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module GHC.Stg.InferTags.Rewrite (rewriteTopBinds)
where

import GHC.Prelude

import GHC.Types.Id
import GHC.Types.Name
import GHC.Types.Unique.Supply
import GHC.Types.Unique.FM
import GHC.Types.RepType
import GHC.Unit.Types (Module)

import GHC.Core.DataCon
import GHC.Core (AltCon(..) )
import GHC.Core.Type

import GHC.StgToCmm.Types

import GHC.Stg.Utils
import GHC.Stg.Syntax as StgSyn

import GHC.Data.Maybe
import GHC.Utils.Panic
import GHC.Utils.Panic.Plain

import GHC.Utils.Outputable
import GHC.Utils.Monad.State.Strict
import GHC.Utils.Misc

import GHC.Stg.InferTags.Types

import Control.Monad
import GHC.Types.Basic (CbvMark (NotMarkedCbv, MarkedCbv), isMarkedCbv, TopLevelFlag(..), isTopLevel)
import GHC.Types.Var.Set

-- import GHC.Utils.Trace
-- import GHC.Driver.Ppr

newtype RM a = RM { unRM :: (State (UniqFM Id TagSig, UniqSupply, Module, IdSet) a) }
    deriving (Functor, Monad, Applicative)

------------------------------------------------------------
-- Add cases around strict fields where required.
------------------------------------------------------------
{-
The work of this pass is simple:
* We traverse the STG AST looking for constructor allocations.
* For all allocations we check if there are strict fields in the constructor.
* For any strict field we check if the argument is known to be properly tagged.
* If it's not known to be properly tagged, we wrap the whole thing in a case,
  which will force the argument before allocation.
This is described in detail in Note [Strict Field Invariant].

The only slight complication is that we have to make sure not to invalidate free
variable analysis in the process.

Note [Partially applied workers]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Sometimes we will get a function f of the form
    -- Arity 1
    f :: Dict a -> a -> b -> (c -> d)
    f dict a b = case dict of
        C m1 m2 -> m1 a b

Which will result in a W/W split along the lines of
    -- Arity 1
    f :: Dict a -> a -> b -> (c -> d)
    f dict a = case dict of
        C m1 m2 -> $wf m1 a b

    -- Arity 4
    $wf :: (a -> b -> d -> c) -> a -> b -> c -> d
    $wf m1 a b c = m1 a b c

It's notable that the worker is called *undersatured* in the wrapper.
At runtime what happens is that the wrapper will allocate a PAP which
once fully applied will call the worker. And all is fine.

But what about a strict worker! Well the function returned by `f` would
be a unknown call, so we lose the ability to enfore the invariant that
cbv marked arguments from StictWorkerId's are actually properly tagged
as the annotations would be unavailable at the (unknown) call site.

The fix is easy. We eta-expand all calls to functions taking call-by-value
arguments during CorePrep just like we do with constructor allocations.

Note [Upholding free variable annotations]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The code generator requires us to maintain exact information
about free variables about closures. Since we convert some
RHSs from constructor allocations to closures we have to provide
fvs of these closures. Not all constructor arguments will become
free variables. Only these which are not bound at the top level
have to be captured.
To facilitate this we keep track of a set of locally bound variables in
the current context which we then use to filter constructor arguments
when building the free variable list.
-}

--------------------------------
-- Utilities
--------------------------------

instance MonadUnique RM where
    getUniqueSupplyM = RM $ do
        (m, us, mod,lcls) <- get
        let (us1, us2) = splitUniqSupply us
        (put) (m,us2,mod,lcls)
        return us1

getMap :: RM (UniqFM Id TagSig)
getMap = RM $ ((\(fst,_,_,_) -> fst) <$> get)

setMap :: (UniqFM Id TagSig) -> RM ()
setMap m = RM $ do
    (_,us,mod,lcls) <- get
    put (m, us,mod,lcls)

getMod :: RM Module
getMod = RM $ ( (\(_,_,thrd,_) -> thrd) <$> get)

getFVs :: RM IdSet
getFVs = RM $ ((\(_,_,_,lcls) -> lcls) <$> get)

setFVs :: IdSet -> RM ()
setFVs fvs = RM $ do
    (tag_map,us,mod,_lcls) <- get
    put (tag_map, us,mod,fvs)

-- Rewrite the RHS(s) while making the id and it's sig available
-- to determine if things are tagged/need to be captured as FV.
withBind :: TopLevelFlag -> GenStgBinding 'InferTaggedBinders -> RM a -> RM a
withBind top_flag (StgNonRec bnd _) cont = withBinder top_flag bnd cont
withBind top_flag (StgRec binds) cont = do
    let (bnds,_rhss) = unzip binds :: ([(Id, TagSig)], [GenStgRhs 'InferTaggedBinders])
    withBinders top_flag bnds cont

addTopBind :: GenStgBinding 'InferTaggedBinders -> RM ()
addTopBind (StgNonRec (id, tag) _) = do
    s <- getMap
    -- pprTraceM "AddBind" (ppr id)
    setMap $ addToUFM s id tag
    return ()
addTopBind (StgRec binds) = do
    let (bnds,_rhss) = unzip binds
    !s <- getMap
    -- pprTraceM "AddBinds" (ppr $ map fst bnds)
    setMap $! addListToUFM s bnds

withBinder :: TopLevelFlag ->  (Id, TagSig) -> RM a -> RM a
withBinder top_flag (id,sig) cont = do
    oldMap <- getMap
    setMap $ addToUFM oldMap id sig
    a <- if isTopLevel top_flag
            then cont
            else withLcl id cont
    setMap oldMap
    return a

withBinders :: TopLevelFlag -> [(Id, TagSig)] -> RM a -> RM a
withBinders TopLevel sigs cont = do
    oldMap <- getMap
    setMap $ addListToUFM oldMap sigs
    a <- cont
    setMap oldMap
    return a
withBinders NotTopLevel sigs cont = do
    oldMap <- getMap
    oldFvs <- getFVs
    setMap $ addListToUFM oldMap sigs
    setFVs $ extendVarSetList oldFvs (map fst sigs)
    a <- cont
    setMap oldMap
    setFVs oldFvs
    return a

-- | Compute the argument with the given set of ids treated as requiring capture
-- as free variables.
withClosureLcls :: DIdSet -> RM a -> RM a
withClosureLcls fvs act = do
    old_fvs <- getFVs
    let fvs' = nonDetStrictFoldDVarSet (flip extendVarSet) old_fvs fvs
    setFVs fvs'
    r <- act
    setFVs old_fvs
    return r

-- | Compute the argument with the given id treated as requiring capture
-- as free variables in closures.
withLcl :: Id -> RM a -> RM a
withLcl fv act = do
    old_fvs <- getFVs
    let fvs' = extendVarSet old_fvs fv
    setFVs fvs'
    r <- act
    setFVs old_fvs
    return r

isTagged :: Id -> RM Bool
isTagged v = do
    this_mod <- getMod
    case nameIsLocalOrFrom this_mod (idName v) of
        True
            | isUnliftedType (idType v)
            -> return True
            | otherwise -> do -- Local binding
                !s <- getMap
                let !sig = lookupWithDefaultUFM s (pprPanic "unknown Id:" (ppr v)) v
                return $ case sig of
                    TagSig info ->
                        case info of
                            TagDunno -> False
                            TagProper -> True
                            TagTagged -> True
                            TagTuple _ -> True -- Consider unboxed tuples tagged.
        False -- Imported
            | Just con <- (isDataConWorkId_maybe v)
            , isNullaryRepDataCon con
            -> return True
            | Just lf_info <- idLFInfo_maybe v
            -> return $
                -- Can we treat the thing as tagged based on it's LFInfo?
                case lf_info of
                    -- Function, applied not entered.
                    LFReEntrant {}
                        -> True
                    -- Thunks need to be entered.
                    LFThunk {}
                        -> False
                    -- LFCon means we already know the tag, and it's tagged.
                    LFCon {}
                        -> True
                    LFUnknown {}
                        -> False
                    LFUnlifted {}
                        -> True
                    LFLetNoEscape {}
                    -- Shouldn't be possible. I don't think we can export letNoEscapes
                        -> True

            | otherwise
            -> return False


isArgTagged :: StgArg -> RM Bool
isArgTagged (StgLitArg _) = return True
isArgTagged (StgVarArg v) = isTagged v

mkLocalArgId :: Id -> RM Id
mkLocalArgId id = do
    !u <- getUniqueM
    return $! setIdUnique (localiseId id) u

---------------------------
-- Actual rewrite pass
---------------------------


rewriteTopBinds :: Module -> UniqSupply -> [GenStgTopBinding 'InferTaggedBinders] -> [TgStgTopBinding]
rewriteTopBinds mod us binds =
    let doBinds = mapM rewriteTop binds

    in evalState (unRM doBinds) (mempty, us, mod, mempty)

rewriteTop :: InferStgTopBinding -> RM TgStgTopBinding
rewriteTop (StgTopStringLit v s) = return $! (StgTopStringLit v s)
rewriteTop (StgTopLifted bind)   = do
    -- Top level bindings can, and must remain in scope
    addTopBind bind
    (StgTopLifted) <$!> (rewriteBinds TopLevel bind)

-- For top level binds, the wrapper is guaranteed to be `id`
rewriteBinds :: TopLevelFlag -> InferStgBinding -> RM (TgStgBinding)
rewriteBinds _top_flag (StgNonRec v rhs) = do
        (!rhs) <-  rewriteRhs v rhs
        return $! (StgNonRec (fst v) rhs)
rewriteBinds top_flag b@(StgRec binds) =
    -- Bring sigs of binds into scope for all rhss
    withBind top_flag b $ do
        (rhss) <- mapM (uncurry rewriteRhs) binds
        return $! (mkRec rhss)
        where
            mkRec :: [TgStgRhs] -> TgStgBinding
            mkRec rhss = StgRec (zip (map (fst . fst) binds) rhss)

-- Rewrite a RHS
rewriteRhs :: (Id,TagSig) -> InferStgRhs
           -> RM (TgStgRhs)
rewriteRhs (_id, _tagSig) (StgRhsCon ccs con cn ticks args) = {-# SCC rewriteRhs_ #-} do
    -- pprTraceM "rewriteRhs" (ppr _id)

    -- Look up the nodes representing the constructor arguments.
    fieldInfos <- mapM isArgTagged args

    -- Filter out non-strict fields.
    let strictFields =
            getStrictConArgs con (zip args fieldInfos) :: [(StgArg,Bool)] -- (nth-argument, tagInfo)
    -- Filter out already tagged arguments.
    let needsEval = map fst . --get the actual argument
                        filter (not . snd) $ -- Keep untagged (False) elements.
                        strictFields :: [StgArg]
    let evalArgs = [v | StgVarArg v <- needsEval] :: [Id]

    if (null evalArgs)
        then return $! (StgRhsCon ccs con cn ticks args)
        else do
            --assert not (isTaggedSig tagSig)
            -- pprTraceM "CreatingSeqs for " $ ppr _id <+> ppr node_id

            -- At this point iff we have  possibly untagged arguments to strict fields
            -- we convert the RHS into a RhsClosure which will evaluate the arguments
            -- before allocating the constructor.
            let ty_stub = panic "mkSeqs shouldn't use the type arg"
            conExpr <- mkSeqs args evalArgs (\taggedArgs -> StgConApp con cn taggedArgs ty_stub)

            fvs <- fvArgs args
            -- lcls <- getFVs
            -- pprTraceM "RhsClosureConversion" (ppr (StgRhsClosure fvs ccs ReEntrant [] $! conExpr) $$ text "lcls:" <> ppr lcls)
            return $! (StgRhsClosure fvs ccs ReEntrant [] $! conExpr)
rewriteRhs _binding (StgRhsClosure fvs ccs flag args body) = do
    withBinders NotTopLevel args $
        withClosureLcls fvs $
            StgRhsClosure fvs ccs flag (map fst args) <$> rewriteExpr False body
        -- return (closure)

fvArgs :: [StgArg] -> RM DVarSet
fvArgs args = do
    fv_lcls <- getFVs
    -- pprTraceM "fvArgs" (text "args:" <> ppr args $$ text "lcls:" <> pprVarSet (fv_lcls) (braces . fsep . map ppr) )
    return $ mkDVarSet [ v | StgVarArg v <- args, elemVarSet v fv_lcls]

type IsScrut = Bool

rewriteExpr :: IsScrut -> InferStgExpr -> RM TgStgExpr
rewriteExpr _ (e@StgCase {})          = rewriteCase e
rewriteExpr _ (e@StgLet {})           = rewriteLet e
rewriteExpr _ (e@StgLetNoEscape {})   = rewriteLetNoEscape e
rewriteExpr isScrut (StgTick t e)     = StgTick t <$!> rewriteExpr isScrut e
rewriteExpr _ e@(StgConApp {})        = rewriteConApp e

rewriteExpr isScrut e@(StgApp {})     = rewriteApp isScrut e
rewriteExpr _ (StgLit lit)           = return $! (StgLit lit)
rewriteExpr _ (StgOpApp op args res_ty) = return $! (StgOpApp op args res_ty)

rewriteCase :: InferStgExpr -> RM TgStgExpr
rewriteCase (StgCase scrut bndr alt_type alts) =
    withBinder NotTopLevel bndr $
        pure StgCase <*>
            rewriteExpr True scrut <*>
            pure (fst bndr) <*>
            pure alt_type <*>
            mapM rewriteAlt alts

rewriteCase _ = panic "Impossible: nodeCase"

rewriteAlt :: InferStgAlt -> RM TgStgAlt
rewriteAlt (altCon, bndrs, rhs) = do
    withBinders NotTopLevel bndrs $ do
        !rhs' <- rewriteExpr False rhs
        return $! (altCon, map fst bndrs, rhs')

rewriteLet :: InferStgExpr -> RM TgStgExpr
rewriteLet (StgLet xt bind expr) = do
    (!bind') <- rewriteBinds NotTopLevel bind
    withBind NotTopLevel bind $ do
        -- pprTraceM "withBindLet" (ppr $ bindersOfX bind)
        !expr' <- rewriteExpr False expr
        return $! (StgLet xt bind' expr')
rewriteLet _ = panic "Impossible"

rewriteLetNoEscape :: InferStgExpr -> RM TgStgExpr
rewriteLetNoEscape (StgLetNoEscape xt bind expr) = do
    (!bind') <- rewriteBinds NotTopLevel bind
    withBind NotTopLevel bind $ do
        !expr' <- rewriteExpr False expr
        return $! (StgLetNoEscape xt bind' expr')
rewriteLetNoEscape _ = panic "Impossible"

rewriteConApp :: InferStgExpr -> RM TgStgExpr
rewriteConApp (StgConApp con cn args tys) = do
    -- We check if the strict field arguments are already known to be tagged.
    -- If not we evaluate them first.
    fieldInfos <- mapM isArgTagged args
    let strictIndices = getStrictConArgs con (zip fieldInfos args) :: [(Bool, StgArg)]
    let needsEval = map snd . filter (not . fst) $ strictIndices :: [StgArg]
    let evalArgs = [v | StgVarArg v <- needsEval] :: [Id]
    if (not $ null evalArgs)
        then do
            -- pprTraceM "Creating conAppSeqs for " $ ppr nodeId <+> parens ( ppr evalArgs ) -- <+> parens ( ppr fieldInfos )
            mkSeqs args evalArgs (\taggedArgs -> StgConApp con cn taggedArgs tys)
        else return $! (StgConApp con cn args tys)

rewriteConApp _ = panic "Impossible"

-- Special case: Expressions like `case x of { ... }`
rewriteApp :: IsScrut -> InferStgExpr -> RM TgStgExpr
rewriteApp True (StgApp f []) = do
    -- pprTraceM "rewriteAppScrut" (ppr f)
    f_tagged <- isTagged f
    -- isTagged looks at more than the result of our analysis.
    -- So always update here if useful.
    let f' = if f_tagged
                then setIdTagSig f (TagSig TagProper)
                else f
    return $! StgApp f' []
rewriteApp _ (StgApp f args)
    -- | pprTrace "rewriteAppOther" (ppr f <+> ppr args) False
    -- = undefined
    | Just marks <- idCbvMarks_maybe f
    , relevant_marks <- dropWhileEndLE (not . isMarkedCbv) marks
    , any isMarkedCbv relevant_marks
    = assert (length relevant_marks <= length args)
      unliftArg relevant_marks

    where
      -- If the function expects any argument to be call-by-value ensure the argument is already
      -- evaluated.
      unliftArg relevant_marks = do
        argTags <- mapM isArgTagged args
        let argInfo = zipWith3 ((,,)) args (relevant_marks++repeat NotMarkedCbv)  argTags :: [(StgArg, CbvMark, Bool)]

            -- untagged cbv argument positions
            cbvArgInfo = filter (\x -> sndOf3 x == MarkedCbv && thdOf3 x == False) argInfo
            cbvArgIds = [x | StgVarArg x <- map fstOf3 cbvArgInfo] :: [Id]
        mkSeqs args cbvArgIds (\cbv_args -> StgApp f cbv_args)

rewriteApp _ (StgApp f args) = return $ StgApp f args
rewriteApp _ _ = panic "Impossible"

-- `mkSeq` x x' e generates `case x of x' -> e`
-- We could also substitute x' for x in e but that's so rarely beneficial
-- that we don't bother.
mkSeq :: Id -> Id -> TgStgExpr -> TgStgExpr
mkSeq id bndr !expr =
    -- pprTrace "mkSeq" (ppr (id,bndr)) $
    let altTy = mkStgAltTypeFromStgAlts bndr [(DEFAULT, [], panic "Not used")]
    in
    StgCase (StgApp id []) bndr altTy [(DEFAULT, [], expr)]

-- `mkSeqs args vs mkExpr` will force all vs, and construct
-- an argument list args' where each v is replaced by it's evaluated
-- counterpart v'.
-- That is if we call `mkSeqs [StgVar x, StgLit l] [x] mkExpr` then
-- the result will be (case x of x' { _DEFAULT -> <mkExpr [StgVar x', StgLit l]>}
{-# INLINE mkSeqs #-} -- We inline to avoid allocating mkExpr
mkSeqs  :: [StgArg] -- ^ Original arguments
        -> [Id]     -- ^ var args to be evaluated ahead of time
        -> ([StgArg] -> TgStgExpr)
                    -- ^ Function that reconstructs the expressions when passed
                    -- the list of evaluated arguments.
        -> RM TgStgExpr
mkSeqs args untaggedIds mkExpr = do
    argMap <- mapM (\arg -> (arg,) <$> mkLocalArgId arg ) untaggedIds :: RM [(InId, OutId)]
    -- mapM_ (pprTraceM "Forcing strict args before allocation:" . ppr) argMap
    let taggedArgs :: [StgArg]
            = map   (\v -> case v of
                        StgVarArg v' -> StgVarArg $ fromMaybe v' $ lookup v' argMap
                        lit -> lit)
                    args

    let conBody = mkExpr taggedArgs
    let body = foldr (\(v,bndr) expr -> mkSeq v bndr expr) conBody argMap
    return $! body

-- Out of all arguments passed at runtime only return these ending up in a
-- strict field
getStrictConArgs :: DataCon -> [a] -> [a]
getStrictConArgs con args
    -- These are always lazy in their arguments.
    | isUnboxedTupleDataCon con = []
    | isUnboxedSumDataCon con = []
    -- For proper data cons we have to check.
    | otherwise =
        [ arg | (arg,MarkedStrict)
                    <- zipEqual "getStrictConArgs"
                                args
                                (dataConRuntimeRepStrictness con)]