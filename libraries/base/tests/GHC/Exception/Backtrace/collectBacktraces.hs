module Main where

import Control.Exception
import GHC.Exception
import GHC.Exception.Backtrace
import System.IO.Unsafe

data CustomException = CustomException deriving (Show)

instance Exception CustomException

main :: IO ()
main = do
  setDefaultBacktraceMechanisms [IPEBacktraceMech, HasCallStackBacktraceMech, CostCenterBacktraceMech]
  print $ collectBacktracesInScrutinee 1

-- Force creation of Stg stack return frames for IPE based backtraces.
collectBacktracesInScrutinee :: Int -> [Backtrace]
collectBacktracesInScrutinee deepness = case scrutinee deepness of
  -- Due the the thrown exception, the cases below are never hit!
  [] -> error "No backtraces at all!"
  bts -> bts
  where
    scrutinee :: Int -> [Backtrace]
    scrutinee 0 = unsafePerformIO $ collectBacktraces
    scrutinee n = scrutinee $ n - 1
