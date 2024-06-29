module SegTreeArray where

import Control.Monad.ST
import Data.Array.ST
import Control.Monad (forM_)

type Index = Int
data Range = Index :--: Index
  deriving (Eq, Show)

newtype SegTree s = SegTree (STUArray s Int Int)

mkSegTree :: [Int] -> ST s (SegTree s)
mkSegTree as = do
  let n = length as
  arr <- newArray (1,2*n-1) 0
  forM_ (zip [n ..] as) $ uncurry (writeArray arr)
  forM_ [n-1, n-2 .. 1] $ \i -> do
    x <- readArray arr (2*i)
    y <- readArray arr (2*i+1)
    writeArray arr i (x+y)
  return (SegTree arr)

update :: Int -> Int -> SegTree s -> ST s ()
update i v (SegTree arr) = go i
  where
    go 0 = return ()
    go j = modifyArray' arr j (+v) >> go (j `div` 2)

rq :: Range -> SegTree s -> ST
rq (i :--: j) (SegTree s)
