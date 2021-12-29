{-# language MagicHash, TransformListComp, GADTs, TypeFamilies #-}
module T20864 where
import GHC.Exts

-- This passes
loom :: [Int] -> [Int]
loom xs = [z | I# x <- xs, let p = x +# 3#, z <- [1 .. I# p], then take 3]


type family F a where
  F a = Int#

data Foo a where
  Foo :: F a -> F a -> Foo a
-- These fail
glum2 :: [Foo Int] -> [Int]
glum2 xs = [I# (x +# y) | Foo x y <- xs, then take 3]

glum :: [Int] -> [Int]
glum xs = [I# p | I# x <- xs, let p = x +# 3#, then take 3]
