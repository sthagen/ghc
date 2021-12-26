module Main where

import Control.Exception
import GHC.Exception
import GHC.Exception.Backtrace
import System.Exit

data CustomException = CustomException deriving (Show)

instance Exception CustomException

-- When an exception is thrown more than one times, it keeps the first backtrace.
main :: IO ()
main = do
  setDefaultBacktraceMechanisms [HasCallStackBacktraceMech]
  catch
    ( catch
        -- Throw for the first time.
        (throw CustomException)
        -- Throw for the second time.
        (\(e :: SomeExceptionWithLocation) -> throw e)
    )
    ( \(e :: SomeExceptionWithLocation) -> case e of
        (SomeExceptionWithLocation _ bts) ->
          case head bts of
            -- Only print the most significant location; i.e. the location
            -- where throw was called.
            HasCallStackBacktrace cs -> print $ last $ getCallStack cs
            _ -> exitFailure
    )
