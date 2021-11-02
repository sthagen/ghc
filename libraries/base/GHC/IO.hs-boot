{-# LANGUAGE Unsafe #-}
{-# LANGUAGE NoImplicitPrelude #-}

module GHC.IO(
    IO(..),
    mplusIO,
    mkUserError
) where

import GHC.Types
import {-# SOURCE #-} GHC.Exception.Type (SomeExceptionWithLocation)

mplusIO :: IO a -> IO a -> IO a
mkUserError :: [Char] -> SomeExceptionWithLocation
