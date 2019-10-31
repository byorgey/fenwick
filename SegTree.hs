{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTSyntax    #-}
{-# LANGUAGE TupleSections #-}

module SegTree where

import           Data.List   (find)
import           Data.Monoid

data SegmentTree a where
  Leaf   :: a -> Int -> SegmentTree a
  Branch :: a -> Int -> Int -> SegmentTree a -> SegmentTree a -> SegmentTree a
  deriving (Show, Functor)

getValue :: SegmentTree a -> a
getValue (Leaf a _)         = a
getValue (Branch a _ _ _ _) = a

mkSegTree :: Monoid a => [a] -> SegmentTree a
mkSegTree as = go 1 n (as ++ replicate (n - length as) mempty)
  where
    Just n = find (>= length as) (iterate (*2) 1)

    go i _ [a] = Leaf a i
    go i j as = Branch (getValue l <> getValue r) i j l r
      where
        (as1, as2) = splitAt h as
        h = (j-i+1) `div` 2
        l = go i (i+h-1) as1
        r = go (i+h) j   as2

-- Range query
rq :: Monoid a => Int -> Int -> SegmentTree a -> a
rq i j st = snd $ rq' i j st

data Visit = NoVisit | Zero | Stop | Recurse

rq' :: Monoid a => Int -> Int -> SegmentTree a -> (SegmentTree (Visit, a), a)
rq' i j (Leaf a k)
  | i <= k && k <= j = (Leaf (Stop,  a) k, a)
  | otherwise        = (Leaf (Zero, a) k, mempty)
rq' i j (Branch a x y l r)
  | y < i || j < x   = (Branch (Zero, a) x y ((NoVisit,) <$> l) ((NoVisit,) <$> r), mempty)
  | i <= x && y <= j = (Branch (Stop,  a) x y ((NoVisit,) <$> l) ((NoVisit,) <$> r), mempty)
  | otherwise        = (Branch (Recurse, a) x y l' r', al <> ar)
    where
      (l', al) = rq' i j l
      (r', ar) = rq' i j r

-- Update
update :: Monoid a => Int -> a -> SegmentTree a -> SegmentTree a
update i d (Leaf a j)
  | i == j    = Leaf (a <> d) i
  | otherwise = Leaf a j         -- shouldn't happen?

update i d b@(Branch a x y l r)
  | i < x || y < i = b
  | otherwise = Branch (a <> d) x y (update i d l) (update i d r)

data NodeState = Active | Inactive

deactivate :: SegmentTree a -> SegmentTree (a, NodeState)
deactivate = go Active
  where
    go s (Leaf a i) = Leaf (a,s) i
    go s (Branch a i j l r) = Branch (a,s) i j (go Active l) (go Inactive r)
