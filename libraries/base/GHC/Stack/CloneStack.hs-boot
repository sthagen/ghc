{-# LANGUAGE NoImplicitPrelude #-}

module GHC.Stack.CloneStack where

import {-# SOURCE #-} GHC.IO (IO (..))
import GHC.Show

data StackSnapshot

data StackEntry
instance Show StackEntry

cloneMyStack :: IO StackSnapshot

decode :: StackSnapshot -> IO [StackEntry]
