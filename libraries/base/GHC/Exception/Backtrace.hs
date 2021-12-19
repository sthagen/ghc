{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_HADDOCK not-home #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Exception.Backtrace
-- Copyright   :  (c) The GHC Team, 2020-2021
-- Authors     :  Ben Gamari, David Eichmann, Sven Tennie
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- Collect Exception backtraces with several mechanisms.
-----------------------------------------------------------------------------

module GHC.Exception.Backtrace
  ( Backtrace (..),
    BacktraceMechanism (..),
    setDefaultBacktraceMechanisms,
    getDefaultBacktraceMechanisms,
    showBacktraces,
    collectBacktraces,
  )
where

import Data.List
import Data.Maybe
import GHC.Base
import {-# SOURCE #-} GHC.ExecutionStack (Location, getStackTrace)
import {-# SOURCE #-} GHC.ExecutionStack.Internal (showStackFrames)
import GHC.IO.Unsafe
import {-# SOURCE #-} GHC.IORef
import GHC.Ptr
import GHC.Show
import {-# SOURCE #-} GHC.Stack
import {-# SOURCE #-} GHC.Stack.CCS
import {-# SOURCE #-} GHC.Stack.CloneStack

-- | An exception backtrace.
--
-- @since 4.15
data Backtrace
  = -- | a cost center profiler backtrace
    CostCenterBacktrace (Ptr GHC.Stack.CCS.CostCentreStack)
  | -- | a stack from 'GHC.Stack.HasCallStack'
    HasCallStackBacktrace GHC.Stack.CallStack
  | -- | a stack unwinding (e.g. DWARF) backtrace
    ExecutionBacktrace [GHC.ExecutionStack.Location]
  | -- | a backtrace from Info Table Provenance Entries
    IPEBacktrace [StackEntry]

-- | @since 4.15
instance Show Backtrace where
  -- TODO
  showsPrec p (CostCenterBacktrace ccs) = showsPrec p ccs
  showsPrec p (HasCallStackBacktrace ccs) = showsPrec p ccs
  showsPrec _ (ExecutionBacktrace ccs) = showStackFrames ccs
  showsPrec p (IPEBacktrace stackEntries) = showsPrec p stackEntries

-- | How to collect a backtrace when an exception is thrown.
data BacktraceMechanism
  = -- | collect a cost center stacktrace (only available when built with profiling)
    CostCenterBacktraceMech
  | -- | use execution stack unwinding with given limit
    ExecutionStackBacktraceMech (Maybe Int)
  | -- | collect backtraces from Info Table Provenance Entries
    IPEBacktraceMech
  deriving (Eq, Show)

showBacktraces :: [Backtrace] -> String
showBacktraces bts = unlines $ intersperse "" $ map show bts

currentBacktraceMechanisms :: IORef [BacktraceMechanism]
currentBacktraceMechanisms = unsafePerformIO $ newIORef []
{-# NOINLINE currentBacktraceMechanisms #-}

-- | Set how 'Control.Exception.throwIO', et al. collect backtraces.
setDefaultBacktraceMechanisms :: [BacktraceMechanism] -> IO ()
setDefaultBacktraceMechanisms = writeIORef currentBacktraceMechanisms

-- | Returns the currently selected 'BacktraceMechanism'.
getDefaultBacktraceMechanisms :: IO [BacktraceMechanism]
getDefaultBacktraceMechanisms = readIORef currentBacktraceMechanisms

-- | Collect a list of 'Backtrace' via all current default 'BacktraceMechanism'.
-- See 'setDefaultBacktraceMechanisms'
collectBacktraces :: IO [Backtrace]
collectBacktraces = do
  mech <- getDefaultBacktraceMechanisms
  catMaybes `fmap` mapM collectBacktraces' mech

-- | Collect a 'Backtrace' via the given 'BacktraceMechanism'.
collectBacktraces' :: BacktraceMechanism -> IO (Maybe Backtrace)
collectBacktraces' CostCenterBacktraceMech = do
  ptr <- getCurrentCCS ()
  return $ if ptr == nullPtr then Nothing else Just (CostCenterBacktrace ptr)
collectBacktraces' (ExecutionStackBacktraceMech _) = fmap ExecutionBacktrace `fmap` getStackTrace
collectBacktraces' IPEBacktraceMech = do
  stack <- cloneMyStack
  stackEntries <- decode stack
  return $ Just $ IPEBacktrace stackEntries
