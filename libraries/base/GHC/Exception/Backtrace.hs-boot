{-# LANGUAGE NoImplicitPrelude #-}

module GHC.Exception.Backtrace
    ( Backtrace
    , collectBacktraces
    ) where

import GHC.Base

data Backtrace

collectBacktraces :: IO [Backtrace]
