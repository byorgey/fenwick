{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTSyntax          #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Data.List (find)

data Range = Int :--: Int
  deriving (Eq, Show)

subR :: Range -> Range -> Bool
(lo1 :--: hi1) `subR` (lo2 :--: hi2) = lo2 <= lo1 && hi1 <= hi2

inR :: Int -> Range -> Bool
k `inR` i = (k :--: k) `subR` i

disjoint :: Range -> Range -> Bool
disjoint (lo1 :--: hi1) (lo2 :--: hi2) = hi1 < lo2 || hi2 < lo1

data SegTree a where
  Empty   :: SegTree a
  Branch  :: a -> Range -> SegTree a -> SegTree a -> SegTree a

update :: Monoid a => Int -> a -> SegTree a -> SegTree a
update _ _ Empty = Empty
update i v b@(Branch a rng l r)
  | i `inR` rng  = Branch (a <> v) rng (update i v l) (update i v r)
  | otherwise    = b

rq :: Monoid a => Range -> SegTree a -> a
rq _ Empty = mempty
rq q (Branch a rng l r)
  | disjoint rng q  = mempty
  | rng `subR` q    = a
  | otherwise       = rq q l <> rq q r

-- mkSegTree :: Monoid a => [a] -> SegTree a
-- mkSegTree as = go (1 :--: n) (as ++ replicate (n - length as) mempty)
--   where
--     Just n = find (>= length as) (iterate (*2) 1)

--     go _   []  = Empty
--     go rng as  = Branch (getValue l <> getValue r) rng l r
--       where
--         (as1, as2) = splitAt h as
--         h = (j-i+1) `div` 2
--         l = go i (i+h-1) as1
--         r = go (i+h) j   as2
