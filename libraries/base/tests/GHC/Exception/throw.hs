module Main where

import Control.Exception
import GHC.Exception
import GHC.Exception.Backtrace
import GHC.Exception.Type
import GHC.IO.Unsafe

data CustomException = CustomException1 | CustomException2 | CustomException3 | CustomException4 deriving (Show)

instance Exception CustomException

main :: IO ()
main = do
  print "=== Test backtraces ==="
  printBacktrace [] 0 CustomException1
  printBacktrace [HasCallStackBacktraceMech] 0 CustomException1
  printBacktrace [CostCenterBacktraceMech] 0 CustomException2
  -- ExecutionStackBacktraceMech unfortunately crashes unless GHC was
  -- configured with '--enable-dwarf-unwind'.
  -- printBacktrace [ExecutionStackBacktraceMech]
  printBacktrace [IPEBacktraceMech] 1 CustomException3
  printBacktrace
    [ IPEBacktraceMech,
      CostCenterBacktraceMech,
      HasCallStackBacktraceMech
    ]
    2
    CustomException4

printBacktrace :: [BacktraceMechanism] -> Int -> CustomException -> IO ()
printBacktrace mechs deepness e = do
  print $ "Backtrace mechanisms " ++ show mechs ++ ":"
  setDefaultBacktraceMechanisms mechs
  _ <- catch
    (produceDeepStack deepness e)
    ( \(e :: SomeExceptionWithLocation) -> case e of
        (SomeExceptionWithLocation _ bts) -> do
            print bts
            pure 42
    )
  pure ()

-- Force creation of Stg stack return frames for IPE based backtraces.
produceDeepStack :: Int -> CustomException -> IO Int
produceDeepStack deepness e = case unsafePerformIO $ getDeepStackCase deepness e of
  -- Due to the thrown exception, the cases below are never hit!
  -- But we need to include some "noise" here, such that GHC doesn't simplify
  -- the case expression away.
  0 -> pure 42
  i -> pure i
  where
    -- Get the exception to throw as parameter, so that GHC cannot use an
    -- already evaluated thunk from a prior execution.
    getDeepStackCase :: Int -> CustomException -> IO Int
    getDeepStackCase 0 e = throw e
    getDeepStackCase n e = getDeepStackCase (n - 1) e
