{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module CStream where

-- XXX can we generalize so the repeating part has more than one element?
-- https://stackoverflow.com/questions/50144990/how-to-implement-an-eventually-repeating-list-in-haskell

import Prelude hiding (repeat, take, drop, (!!), zipWith, foldMap, and, or, all, any, maximum, minimum)
import Data.Monoid (All(..), Any(..))
import Data.Semigroup (Max(..), Min(..))

data S a = Rep a | Cons a !(S a)
  deriving (Functor)

expand :: S a -> S a
expand (Rep a) = Cons a (Rep a)
expand as = as

infixr 5 :::
pattern (:::) :: Eq a => a -> S a -> S a
pattern (:::) a as <- (expand -> Cons a as)
  where
    a' ::: Rep a | a' == a = Rep a
    a ::: as = Cons a as

{-# COMPLETE (:::) #-}

instance Eq a => Eq (S a) where
  Rep a == Rep b = a == b
  (a ::: as) == (b ::: bs) = a == b && as == bs

repeat :: a -> S a
repeat = Rep

head :: Eq a => S a -> a
head (a ::: _) = a

tail :: Eq a => S a -> S a
tail (_ ::: as) = as

take :: Eq a => Int -> S a -> [a]
take n _ | n <= 0 = []
take n (a ::: as) = a : take (n-1) as

drop :: Eq a => Int -> S a -> S a
drop n s | n <= 0 = s
drop n (_ ::: as) = drop (n-1) as

(!!) :: Eq a => S a -> Int -> a
(a ::: _) !! 0 = a
Rep a !! _ = a
(_ ::: as) !! n = as !! (n-1)

zipWith :: (Eq a, Eq b, Eq c) => (a -> b -> c) -> S a -> S b -> S c
zipWith f (Rep a) (Rep b) = Rep (f a b)
zipWith f (a ::: as) (b ::: bs) = f a b ::: zipWith f as bs

instance (Show a, Eq a) => Show (S a) where
  show c = '[' : go c
    where
      go :: S a -> String
      go (Rep a) = show a ++ "...]"
      go (a ::: as) = show a ++ "," ++ go as

class Semigroup m => IdempotentSemigroup m

instance IdempotentSemigroup All
instance IdempotentSemigroup Any
instance Ord a => IdempotentSemigroup (Max a)
instance Ord a => IdempotentSemigroup (Min a)

-- Can do stuff from Foldable that uses an idempotent monoid.  Can't
-- make Foldable instance because of Eq constraint (and it wouldn't
-- really be lawful anyway).
foldMap :: (Eq a, IdempotentSemigroup m) => (a -> m) -> S a -> m
foldMap f (Rep a) = f a
foldMap f (a ::: as) = f a <> foldMap f as

and :: S Bool -> Bool
and = getAll . foldMap All

or :: S Bool -> Bool
or = getAny . foldMap Any

all :: (a -> Bool) -> S a -> Bool
all f = and . fmap f

any :: (a -> Bool) -> S a -> Bool
any f = or . fmap f

maximum :: Ord a => S a -> a
maximum = getMax . foldMap Max

minimum :: Ord a => S a -> a
minimum = getMin . foldMap Min
