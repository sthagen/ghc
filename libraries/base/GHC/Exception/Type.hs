{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_HADDOCK not-home #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Exception.Type
-- Copyright   :  (c) The University of Glasgow, 1998-2002
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- Exceptions and exception-handling functions.
--
-----------------------------------------------------------------------------

module GHC.Exception.Type
       ( -- * Fundamentals
         Exception(..)
       , SomeException(..)
       , SomeExceptionWithLocation(..)
       , addBacktrace
         -- * Concrete exception types
       , ArithException(..)
       , divZeroException, overflowException, ratioZeroDenomException
       , underflowException
       ) where

import GHC.Exception.Backtrace (Backtrace, showBacktraces)

import Data.Maybe
import Data.Typeable (Typeable, cast, typeOf)
   -- loop: Data.Typeable -> GHC.Err -> GHC.Exception
import GHC.Base
import GHC.Show
import Data.List (isPrefixOf)

{- |
The @SomeExceptionWithLocation@ type is the root of the exception type hierarchy.
When an exception of type @e@ is thrown, behind the scenes it is
encapsulated in a @SomeException@.

@since 4.16.0.0
-}
data SomeExceptionWithLocation = SomeExceptionWithLocation [Backtrace] SomeException

addBacktrace :: Backtrace -> SomeExceptionWithLocation -> SomeExceptionWithLocation
addBacktrace bt (SomeExceptionWithLocation bts e) =
    SomeExceptionWithLocation (bt : bts) e

{- |
The @SomeException@ type represents any exception. This used to be the root of
the exception type hierarchy, although this role is now played by
'SomeExceptionWithLocation'
-}
data SomeException = forall e. Exception e => SomeException e

-- | @since 3.0
instance Show SomeExceptionWithLocation where
        -- TODO: Should this obey the usual Show-is-Haskell invariant?
    showsPrec p (SomeExceptionWithLocation bts e) =
        showsPrec p e . showString (showBacktraces bts)

-- | @since 3.0
instance Show SomeException where
    showsPrec p (SomeException e) = showsPrec p e


{- |
Any type that you wish to throw or catch as an exception must be an
instance of the @Exception@ class. The simplest case is a new exception
type directly below the root:

> data MyException = ThisException | ThatException
>     deriving Show
>
> instance Exception MyException

The default method definitions in the @Exception@ class do what we need
in this case. You can now throw and catch @ThisException@ and
@ThatException@ as exceptions:

@
*Main> throw ThisException \`catch\` \\e -> putStrLn (\"Caught \" ++ show (e :: MyException))
Caught ThisException
@

In more complicated examples, you may wish to define a whole hierarchy
of exceptions:

> ---------------------------------------------------------------------
> -- Make the root exception type for all the exceptions in a compiler
>
> data SomeCompilerException = forall e . Exception e => SomeCompilerException e
>
> instance Show SomeCompilerException where
>     show (SomeCompilerException e) = show e
>
> instance Exception SomeCompilerException
>
> compilerExceptionToException :: Exception e => e -> SomeException
> compilerExceptionToException = toException . SomeCompilerException
>
> compilerExceptionFromException :: Exception e => SomeException -> Maybe e
> compilerExceptionFromException x = do
>     SomeCompilerException a <- fromException x
>     cast a
>
> ---------------------------------------------------------------------
> -- Make a subhierarchy for exceptions in the frontend of the compiler
>
> data SomeFrontendException = forall e . Exception e => SomeFrontendException e
>
> instance Show SomeFrontendException where
>     show (SomeFrontendException e) = show e
>
> instance Exception SomeFrontendException where
>     toException = compilerExceptionToException
>     fromException = compilerExceptionFromException
>
> frontendExceptionToException :: Exception e => e -> SomeException
> frontendExceptionToException = toException . SomeFrontendException
>
> frontendExceptionFromException :: Exception e => SomeException -> Maybe e
> frontendExceptionFromException x = do
>     SomeFrontendException a <- fromException x
>     cast a
>
> ---------------------------------------------------------------------
> -- Make an exception type for a particular frontend compiler exception
>
> data MismatchedParentheses = MismatchedParentheses
>     deriving Show
>
> instance Exception MismatchedParentheses where
>     toException   = frontendExceptionToException
>     fromException = frontendExceptionFromException

We can now catch a @MismatchedParentheses@ exception as
@MismatchedParentheses@, @SomeFrontendException@ or
@SomeCompilerException@, but not other types, e.g. @IOException@:

@
*Main> throw MismatchedParentheses \`catch\` \\e -> putStrLn (\"Caught \" ++ show (e :: MismatchedParentheses))
Caught MismatchedParentheses
*Main> throw MismatchedParentheses \`catch\` \\e -> putStrLn (\"Caught \" ++ show (e :: SomeFrontendException))
Caught MismatchedParentheses
*Main> throw MismatchedParentheses \`catch\` \\e -> putStrLn (\"Caught \" ++ show (e :: SomeCompilerException))
Caught MismatchedParentheses
*Main> throw MismatchedParentheses \`catch\` \\e -> putStrLn (\"Caught \" ++ show (e :: IOException))
*** Exception: MismatchedParentheses
@

-}
class (Typeable e, Show e) => Exception e where
    toException   :: e -> SomeExceptionWithLocation
    fromException :: SomeExceptionWithLocation -> Maybe e

    -- TODO: This is only a helper function to inspect how an Exception is layered / structured -> remove
    toTypeString  :: e -> String

    -- TODO: Remove invariant assertion
    toException e = if isPrefixOf "SomeException" (toTypeString e) then
                      error "toException - Unexpected nesting of SomeException"
                    else
                      SomeExceptionWithLocation [] $ SomeException e

    -- TODO: Remove invariant assertion
    fromException (SomeExceptionWithLocation _ (SomeException e)) =
                    if isPrefixOf "SomeException" (toTypeString e) then
                      error "fromException - Unexpected nesting of SomeException"
                    else
                      cast e

    toTypeString e = show $ typeOf e

    -- | Render this exception value in a human-friendly manner.
    --
    -- Default implementation: @'show'@.
    --
    -- @since 4.8.0.0
    displayException :: e -> String
    displayException = show

-- | @since 4.16.0.0
instance Exception SomeExceptionWithLocation where
    toException se = se
    fromException = Just
    displayException (SomeExceptionWithLocation bt (SomeException e)) = displayException e <> showBacktraces bt
    toTypeString (SomeExceptionWithLocation _ e) = "SomeExceptionWithLocation " ++ toTypeString e

-- | @since 3.0
instance Exception SomeException where
    toException e = SomeExceptionWithLocation [] e
    fromException (SomeExceptionWithLocation _ (SomeException e)) = Just (SomeException e)
    displayException (SomeException e) = displayException e
    toTypeString (SomeException e) = "SomeException " ++ toTypeString e


-- |Arithmetic exceptions.
data ArithException
  = Overflow
  | Underflow
  | LossOfPrecision
  | DivideByZero
  | Denormal
  | RatioZeroDenominator -- ^ @since 4.6.0.0
  deriving ( Eq  -- ^ @since 3.0
           , Ord -- ^ @since 3.0
           )

divZeroException, overflowException, ratioZeroDenomException, underflowException  :: SomeExceptionWithLocation
divZeroException        = toException DivideByZero
overflowException       = toException Overflow
ratioZeroDenomException = toException RatioZeroDenominator
underflowException      = toException Underflow

-- | @since 4.0.0.0
instance Exception ArithException

-- | @since 4.0.0.0
instance Show ArithException where
  showsPrec _ Overflow        = showString "arithmetic overflow"
  showsPrec _ Underflow       = showString "arithmetic underflow"
  showsPrec _ LossOfPrecision = showString "loss of precision"
  showsPrec _ DivideByZero    = showString "divide by zero"
  showsPrec _ Denormal        = showString "denormal"
  showsPrec _ RatioZeroDenominator = showString "Ratio has zero denominator"
