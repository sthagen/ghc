module Main where

import Control.Exception
import GHC.Exception

data CustomException = CustomException deriving (Show)

instance Exception CustomException

main :: IO ()
main =
  catch
    (throwWithCostCenterStack CustomException)
    ( \(e :: SomeExceptionWithLocation) -> case e of
        SomeExceptionWithLocation _ bts -> print bts
    )
