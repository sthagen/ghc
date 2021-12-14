{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module GHC.Cmm.Alias
    ( AbsMem(..)
    , bothHeaps, heapsConflict, bothMems
    , memConflicts, exprMem, loadAddr, storeAddr

    , cmmHpAlias, get_node_hps, HpSet(..), elemHpSet
    , sizeHpSet

    ,lintHpReads)
where

import GHC.Prelude as Prelude

import GHC.Platform
import GHC.Cmm
import GHC.Cmm.Ppr.Expr () -- For Outputable instances
import GHC.Cmm.Ppr () -- For Outputable instances
import GHC.Cmm.Dataflow.Collections
import GHC.Cmm.Dataflow
import GHC.Cmm.Dataflow.Label

import GHC.Utils.Outputable

import Data.Set as Set
import Data.Semigroup
import GHC.Utils.Panic (panic)
import GHC.Cmm.Dataflow.Block (blockSplit, blockToList)
import GHC.Cmm.Utils (regUsedIn, toBlockList)
import GHC.Utils.Trace (pprTrace)
import Data.List (mapAccumL)

-----------------------------------------------------------------------------
-- Abstracting over memory access
-----------------------------------------------------------------------------

-- An abstraction of memory read or written.
data AbsMem
  = NoMem            -- no memory accessed
  | AnyMem           -- arbitrary memory
  | HeapMem !HeapType
  | StackMem         -- definitely stack memory
  | SpMem            -- <size>[Sp+n]
       {-# UNPACK #-} !Int
       {-# UNPACK #-} !Int
  deriving Show

instance Outputable AbsMem where
  ppr x = parens (text . show $ x)

data HeapType = OldHeap | NewHeap | AnyHeap deriving (Show,Eq)

bothHeaps :: HeapType -> HeapType -> HeapType
bothHeaps h1 h2 | h1 == h2 = h1
bothHeaps _  _  = AnyHeap

heapsConflict :: HeapType -> HeapType -> Bool
heapsConflict (AnyHeap) (_) = True
heapsConflict (_) (AnyHeap) = True
heapsConflict (OldHeap) (NewHeap) = False
heapsConflict (NewHeap) (OldHeap) = False
heapsConflict (_) (_) = True



{- Note [Heap Kinds]
~~~~~~~~~~~~~~~~~~~~
Our goal is to allow sinking into assignments to Hp.
That is for a sequence like:

  c1 = [R1 + 8]
  c2 = [R1 + 16]
  [Hp-16] = c1
  [Hp-8] = c2

We want to inline the assignments to get:

  [Hp-16] = [R1 + 8]
  [Hp-8] = [R1 + 16]

To achieve this we split heap memory references into three kinds.
OldHeap, NewHeap, AnyHeap.

* Reading from heap memory is defined to be OldHeap.
* Writing to HpReg is defined to be a reference to NewHeap.
* Reading from Hp for assignmentsis defined to be AnyHeap


New/OldHeap don't conflict. All other references do conflict.

Examples

  c1 = [R1 + 8]
  [Hp-16] = c1
  => Can be sunk as Old/New don't conflict.

  [Hp-16] = c1
  d = [Hp-24]
  [Hp-24] = c2
  e = d
  => The assignment to d conflicts with the write to [Hp-24].
     `[Hp-24]` is AnyHeap which will conflict with a write to NewHeap.

-- Dangerous, but works out fine.
  x = [Hp-16]
  y = x
  [Hp-16] = 0
  z = x
=> We would drop the assignment to x before the write to [Hp-16]

This is of course a hack. Because we will sink into an assignment
to [Hp-8], but not into one for x = Hp; [x-8].
Even though they are the same.

It also depends on Hp never being used to write to "old" heap. This
isn't something our code generation ever does, so that seems fine.

It makes easy to break this optimization in Hand-written Cmm though.
Not sure it matters. Code that uses HP to alias non-newly allocated
heap seems pretty out there.

-----------------------

Informally we can look at why this is safe. If we trip on aliasing it
means we sink a read *past* an aliased write.

That is we start semantically with a variant of: x = [mem1]; [mem2] = y but rewrite
it later to [mem2] = y; x = [mem1]. Where mem1 and mem2 are aliased.

What prevents this is the `conflicts` check on stores.
In broad strokes we are checking for `memConflicts (memExpr [mem1]) (storeAddr [mem2]).

We haven't changed the behaviour for heap vs non-heap memory. So the only way we introduce
failure is if *both* expressions are determined to be some kind of heap memory.

We have these combinations:

Store | Load -> Resolution
~~~~~~~~~~~~~~~~~~~~~~~~
  Any | _    -> Conflicts
  _   | Any  -> Conflicts
  New | New  -> Conflicts
  Old | Old  -> Conflicts
  New | Old  -> No conflict
  Old | New  -> Impossible

Old|New is impossible since loads only get assigned HeapAny or HeapOld.
This leaves the combination of New|Old.

New implies the store is of the kind `[Hp+offset] = <e>`. (See `storeAddr`).
While Old implies the RHS of the assignment we went to sink past the store:
* Does not mention Hp (or we would get Any instead of Old)
* Mentions some Gc pointer.

So we can narrow down our failure modes to a pattern of the kind:

foo = [gcPtr<op>e]
[Hp+off] = <e>

The failure case then becomes that gcPtr<op>e and [Hp+off] alias. Can this arise?

bar = Hp + off
foo = [bar]
[Hp+off] = <e>

If bar isn't sunk into foo then we indeed we can end up with:

1 bar = Hp + off
3 [Hp+off] = <e>
2 foo = [bar]

This is because foo looks like a regular GcPtr to CmmSink. God damnit.
We could avoid this by making "references Hp" a transitive property.

Not sure how to best do this though.

-}

-- Having SpMem is important because it lets us float loads from Sp
-- past stores to Sp as long as they don't overlap, and this helps to
-- unravel some long sequences of
--    x1 = [Sp + 8]
--    x2 = [Sp + 16]
--    ...
--    [Sp + 8]  = xi
--    [Sp + 16] = xj
--
-- Note that SpMem is invalidated if Sp is changed, but the definition
-- of 'conflicts' above handles that.

-- ToDo: this won't currently fix the following commonly occurring code:
--    x1 = [R1 + 8]
--    x2 = [R1 + 16]
--    ..
--    [Hp - 8] = x1
--    [Hp - 16] = x2
--    ..

-- because [R1 + 8] and [Hp - 8] are both HeapMem.  We know that
-- assignments to [Hp + n] do not conflict with any other heap memory,
-- but this is tricky to nail down.  What if we had
--
--   x = Hp + n
--   [x] = ...
--
--  the store to [x] should be "new heap", not "old heap".
--  Furthermore, you could imagine that if we started inlining
--  functions in Cmm then there might well be reads of heap memory
--  that was written in the same basic block.  To take advantage of
--  non-aliasing of heap memory we will have to be more clever.

-- Note [Foreign calls clobber heap]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- It is tempting to say that foreign calls clobber only
-- non-heap/stack memory, but unfortunately we break this invariant in
-- the RTS.  For example, in stg_catch_retry_frame we call
-- stmCommitNestedTransaction() which modifies the contents of the
-- TRec it is passed (this actually caused incorrect code to be
-- generated).
--
-- Since the invariant is true for the majority of foreign calls,
-- perhaps we ought to have a special annotation for calls that can
-- modify heap/stack memory.  For now we just use the conservative
-- definition here.
--
-- Some CallishMachOp imply a memory barrier e.g. AtomicRMW and
-- therefore we should never float any memory operations across one of
-- these calls.
--
-- `suspendThread` releases the capability used by the thread, hence we mustn't
-- float accesses to heap, stack or virtual global registers stored in the
-- capability (e.g. with unregisterised build, see #19237).

bothMems :: AbsMem -> AbsMem -> AbsMem
bothMems NoMem    x         = x
bothMems x        NoMem     = x
bothMems (HeapMem h1) (HeapMem h2) = HeapMem $! bothHeaps h1 h2
bothMems StackMem StackMem     = StackMem
bothMems (SpMem o1 w1) (SpMem o2 w2)
  | o1 == o2  = SpMem o1 (max w1 w2)
  | otherwise = StackMem
bothMems SpMem{}  StackMem  = StackMem
bothMems StackMem SpMem{}   = StackMem
bothMems _         _        = AnyMem

memConflicts :: AbsMem -> AbsMem -> Bool
memConflicts NoMem      _          = False
memConflicts _          NoMem      = False
memConflicts HeapMem{}  StackMem   = False
memConflicts StackMem   HeapMem{}  = False
memConflicts SpMem{}    HeapMem{}  = False
memConflicts HeapMem{}  SpMem{}    = False
memConflicts (HeapMem h1) (HeapMem h2) = heapsConflict h1 h2
memConflicts (SpMem o1 w1) (SpMem o2 w2)
  | o1 < o2   = o1 + w1 > o2
  | otherwise = o2 + w2 > o1
memConflicts _         _         = True

exprMem :: Platform -> CmmExpr -> AbsMem
exprMem platform (CmmLoad addr w) = bothMems (loadAddr platform addr (typeWidth w)) (exprMem platform addr)
exprMem platform (CmmMachOp _ es) = Prelude.foldr bothMems NoMem (fmap (exprMem platform) es)
exprMem _        _                = NoMem

loadAddr, storeAddr :: Platform -> CmmExpr -> Width -> AbsMem
loadAddr p = refAddr p False
storeAddr p = refAddr p True

refAddr :: Platform -> Bool -> CmmExpr -> Width -> AbsMem
refAddr platform is_store e w =
  case e of
   CmmReg r       -> regAddr platform is_store r 0 w
   CmmRegOff r i  -> regAddr platform is_store r i w
   _other | regUsedIn platform spReg e -> StackMem
          | otherwise                  -> -- pprTrace "refAddrAny" (ppr e)
                                          AnyMem

regAddr :: Platform -> Bool -> CmmReg -> Int -> Width -> AbsMem
regAddr _ _store   (CmmGlobal Sp) i w = SpMem i (widthInBytes w)
regAddr _ is_store (CmmGlobal Hp) _ _
    | is_store  = HeapMem NewHeap
    | otherwise = panic hp_mem_msg -- HeapMem AnyHeap
regAddr _ __store   (CmmGlobal CurrentTSO) _ _ = HeapMem (AnyHeap) -- important for PrimOps
regAddr platform is_store r _ _
    | isGcPtrType (cmmRegType platform r)
    = if is_store
          then (HeapMem AnyHeap)
          else (HeapMem OldHeap) -- yay! GCPtr pays for itself
regAddr _ _store _ _ _ = AnyMem

-----------------------------------------------------------------------------
-- Abstracting over memory access - considering which registers might alias to Hp
--
-- Currently these will panic when trying to load values via Hp or Hp aliased
-- expressions. If we ever allow use of Hp for memory reads then we need to return
-- AnyHeap instead.
-----------------------------------------------------------------------------

exprMemHp :: Platform -> HpSet -> CmmExpr -> AbsMem
exprMemHp platform hps (CmmLoad addr w) = pprTrace "exprMemHp" (ppr addr) $ bothMems (loadAddrHp platform hps addr (typeWidth w)) (exprMemHp platform hps addr)
exprMemHp platform hps (CmmMachOp _ es) = pprTrace "exprMemHp" (ppr es) $ Prelude.foldr (\l r -> l `seq` r `seq` bothMems l r) NoMem (fmap (exprMemHp platform hps) es)
exprMemHp _        _   _                = NoMem

loadAddrHp, storeAddrHp :: Platform -> HpSet -> CmmExpr -> Width -> AbsMem
loadAddrHp p hps = refAddrHp p hps False
storeAddrHp p hps = refAddrHp p hps True

refAddrHp :: Platform -> HpSet -> Bool -> CmmExpr -> Width -> AbsMem
refAddrHp platform hps is_store e w = pprTrace "refAddrHp" (ppr e) $
  case e of
   CmmReg r       -> regAddrHp platform hps is_store r 0 w
   CmmRegOff r i  -> regAddrHp platform hps is_store r i w
   _other | regUsedIn platform spReg e -> StackMem
          | foldRegsUsed platform (\b r -> b || r `elemHpSet` hps) False e -> panic hp_mem_msg
          | otherwise                  -> -- pprTrace "refAddrAny" (ppr e)
                                          AnyMem

regAddrHp :: Platform -> HpSet -> Bool -> CmmReg -> Int -> Width -> AbsMem
regAddrHp _ _hps _store   (CmmGlobal Sp) i w = SpMem i (widthInBytes w)
regAddrHp _ _hps is_store (CmmGlobal Hp) _ _
    | is_store  = HeapMem NewHeap
    | otherwise = panic hp_mem_msg -- HeapMem AnyHeap
regAddrHp _ _hps _store   (CmmGlobal CurrentTSO) _ _ = HeapMem (AnyHeap) -- important for PrimOps
regAddrHp platform hps is_store r _ _
    | isGcPtrType (cmmRegType platform r)
    = if is_store
          then (HeapMem AnyHeap)
          else if r `elemHpSet` hps
              then panic hp_mem_msg -- Depends on Hp in some way. So be conservative.
              else (HeapMem OldHeap) -- yay! GCPtr pays for itself
regAddrHp _ _hps _store _ _ _ = AnyMem

hp_mem_msg :: String
hp_mem_msg =
    "Cmm Hp invariant violated. The NCG backend currently assumes that\n" ++
    "we never use Hp to read from memory. Nor any values which alias to Hp.\n" ++
    "If you are using hand-written Cmm please adjust your code accordingly.\n" ++
    "If you are not please report this as a GHC bug.\n"

-----------------------------------------------------------------------------
-- Calculating what variables transitively depend on the value of Hp on block entry.
-----------------------------------------------------------------------------

-- | The variables aliased to HP on entry to a block
data HpSet = HpSet { localSet :: !LocalRegSet, globalSet :: !GlobalRegSet }

instance Outputable HpSet where
    ppr (HpSet local global) = parens (text "HpSet" <+> text "local:" <+> ppr (regSetToList local) <+> ppr (regSetToList global))

instance Semigroup HpSet where
    (<>) = plusHpSet

instance Monoid HpSet where
    mempty = emptyHpSet

sizeHpSet :: HpSet -> Int
sizeHpSet (HpSet l g) = sizeRegSet l + sizeRegSet g

plusHpSet :: HpSet -> HpSet -> HpSet
plusHpSet (HpSet l1 g1) (HpSet l2 g2) = HpSet (plusRegSet l1 l2) (plusRegSet g1 g2) :: HpSet

elemHpSet :: CmmReg -> HpSet -> Bool
elemHpSet reg hp_set = go reg hp_set
    where go (CmmLocal r)  (HpSet l_set _g_set) = elemRegSet r l_set
          go (CmmGlobal r)  (HpSet _l_set g_set) = elemRegSet r g_set

emptyHpSet :: HpSet
emptyHpSet = HpSet mempty mempty

-- | The dataflow lattice
hpLattice :: DataflowLattice (HpSet)
hpLattice = DataflowLattice emptyHpSet add
  where
    add (OldFact old@(HpSet lold gold)) (NewFact (HpSet lnew gnew)) =
        let !changed = (Set.size l_join + Set.size g_join > Set.size lold + Set.size gold)
            join@(HpSet l_join g_join) = HpSet (Set.union lold lnew) (Set.union gold gnew)
        in if changed then changedIf changed join
                      else changedIf changed old

-- Compute info for one node
get_node_hps
    ::  ( OutputableP Platform (CmmNode e x)
        )
    => Platform -> (CmmNode e x) -> HpSet -> HpSet
get_node_hps platform node hp_set@(HpSet lset gset) =
    let !result_aliases_hp =
            case node of
                -- All calls implicitly depend on Hp so that's useless to use foldRegsUsed on the node.
                -- We really only care if any of the arguments more diretly alias
                -- to Hp, or if Hp itself is used as argument.
                CmmCall{cml_args_regs = arg_regs} -> (foldRegsUsed platform (\b r -> b || (r /= hpReg && r `elemHpSet` hp_set)) False node) || Hp `elem` arg_regs
                _default -> ( foldRegsUsed platform (\b r -> b || r == hpReg || r `elemHpSet` hp_set) False node)

        {-# INLINE update #-}
        update :: forall r. (Ord r,Outputable r) => RegSet r -> r -> RegSet r
        update s r = if result_aliases_hp
            then -- pprTrace "Adding hp" (ppr r <+> pdoc platform node) $
                 extendRegSet s r
            else deleteFromRegSet s r

        g_hps = foldRegsDefd platform (\s reg -> update s reg) gset node :: GlobalRegSet
        l_hps = foldRegsDefd platform (\s reg -> update s reg) lset node :: LocalRegSet

        in (HpSet l_hps g_hps)

xferHp :: Platform -> TransferFun HpSet
xferHp p = blockTransferFwd p hpLattice get_node_hps

-- Blocks that might alias to Hp on *entry*
cmmHpAlias :: Platform -> CmmGraph -> LabelMap HpSet
cmmHpAlias platform graph =
    analyzeCmmFwd hpLattice (xferHp platform) graph mapEmpty

lintHpReads :: Platform -> CmmGraph -> Bool
lintHpReads platform graph =
    Prelude.foldl' lintBlock True blocks
    where
        -- hp aliases on entry to *blocks*
        hp_map = -- pprTraceIt "HpAliasing:" $
                 cmmHpAlias platform graph
        blocks = toBlockList graph

        lintBlock :: Bool -> CmmBlock -> Bool
        lintBlock ok block =
            ok && all (lintNode) annot_middles && lintNode (final_hp_set,exit)
            where
                lbl = entryLabel block
                (_entry,middles,exit) = blockSplit block
                -- nodes and current hp-aliasing *before* the node.
                (final_hp_set, annot_middles) = annotateHps hp_set(blockToList middles)
                -- aliasing on entry to block.
                hp_set
                    | lbl == g_entry graph = mapFindWithDefault mempty lbl hp_map
                    | otherwise = mapFindWithDefault (panic "HpMap - block not found") lbl hp_map

        annotateHps :: HpSet -> [(CmmNode O O)] -> (HpSet, [(HpSet,CmmNode O O)])
        annotateHps hp_set nodes = mapAccumL ann hp_set nodes
            where ann hps (n) = (get_node_hps platform n hps, (hps,n))

        lintNode :: (HpSet,CmmNode e x) -> Bool
        lintNode (hp_set,node) =
            -- pprTrace "LintNode" (pdoc platform node $$ ppr hp_set) $
            case node of
                (CmmStore addr expr) -> storeAddrHp platform hp_set addr `seq` exprMemHp platform hp_set expr `seq` True
                _ -> let has_hp_ref = foldExpDeep (\e !_ -> exprMemHp platform hp_set e `seq` ()) node () :: ()
                     in has_hp_ref `seq` True