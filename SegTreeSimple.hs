{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTSyntax          #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Data.List (find)

data Interval = Int :--: Int
  deriving (Eq, Show)

inI :: Int -> Interval -> Bool
k `inI` i = (k :--: k) `subI` i

subI :: Interval -> Interval -> Bool
(lo1 :--: hi1) `subI` (lo2 :--: hi2) = lo2 <= lo1 && hi1 <= hi2

disjoint :: Interval -> Interval -> Bool
disjoint (lo1 :--: hi1) (lo2 :--: hi2) = hi1 < lo2 || hi2 < lo1

data SegmentTree a where
  Empty   :: SegmentTree a
  Branch  :: a -> Interval -> SegmentTree a -> SegmentTree a -> SegmentTree a
  deriving (Show, Functor)

update :: Monoid a => Int -> a -> SegmentTree a -> SegmentTree a
update _ _ Empty = Empty
update k d b@(Branch a i l r)
  | k `inI` i  = Branch (a <> d) i (update k d l) (update k d r)
  | otherwise  = b

rq :: Monoid a => Interval -> SegmentTree a -> a
rq _ Empty = mempty
rq q (Branch a i l r)
  | disjoint i q  = mempty
  | i `subI` q    = a
  | otherwise     = rq q l <> rq q r

------------------------------------------------------------

infix 1 :--:

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
