{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTSyntax          #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Data.List (find)

data Interval = Int :--: Int
  deriving (Eq, Show)

infix 1 :--:

(∈) :: Int -> Interval -> Bool
k ∈ i = (k :--: k) ⊆ i

(⊆) :: Interval -> Interval -> Bool
(l1 :--: h1) ⊆ (l2 :--: h2) = l2 <= l1 && h1 <= h2

disjoint :: Interval -> Interval -> Bool
disjoint (l1 :--: h1) (l2 :--: h2) = h1 < l2 || h2 < l1

data SegmentTree a where
  Empty  :: SegmentTree a
  Branch :: a -> Interval -> SegmentTree a -> SegmentTree a -> SegmentTree a
  deriving (Show, Functor)

update :: Monoid a => Int -> a -> SegmentTree a -> SegmentTree a
update _ _ Empty = Empty
update k d b@(Branch a i l r)
  | k ∈ i     = Branch (a <> d) i (update k d l) (update k d r)
  | otherwise = b

rq :: Monoid a => Interval -> SegmentTree a -> a
rq _ Empty = mempty
rq q (Branch a i l r)
  | disjoint i q = mempty
  | i ⊆ q        = a
  | otherwise    = rq q l <> rq q r

------------------------------------------------------------

leaf :: a -> Interval -> SegmentTree a
leaf a i = Branch a i Empty Empty

lengthI :: Interval -> Int
lengthI (lo :--: hi) = hi - lo + 1

splitAtI :: Int -> Interval -> (Interval, Interval)
splitAtI x (lo :--: hi) = (lo :--: lo+x-1, lo+x :--: hi)

getValue :: Monoid a => SegmentTree a -> a
getValue Empty            = mempty
getValue (Branch a _ _ _) = a

mkSegTree :: forall a. Monoid a => [a] -> SegmentTree a
mkSegTree as = go (1 :--: n) (as ++ replicate (n - length as) mempty)
  where
    Just n = find (>= length as) (iterate (*2) 1)

    go :: Interval -> [a] -> SegmentTree a
    go i [a] = leaf a i
    go i as  = Branch (getValue l <> getValue r) i l r
      where
        (as1, as2) = splitAt h as
        (i1, i2)   = splitAtI h i
        h = lengthI i `div` 2
        l = go i1 as1
        r = go i2 as2
