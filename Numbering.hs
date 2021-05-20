module Numbering where

import           Control.Arrow (first)
import           Data.Bits

s 0 = [1]
s n = interleave2 [2^n, 2^n + 2 ..] (s (n-1))

interleave2 [] _          = []
interleave2 _ []          = []
interleave2 (a:as) (b:bs) = a : b : interleave2 as bs

interleave [] _      = []
interleave (x:xs) ys = x : interleave ys xs

lsh :: Integer -> Integer
lsh = (`shiftL` 1)

rsh :: Integer -> Integer
rsh = (`shiftR` 1)

shiftOut1 = rsh . shiftTo1

shiftTo1 = while even rsh

while p f = head . dropWhile p . iterate f


-- Lemma:
--     (+1) . lsh . shiftOut1
--   = (+1) . lsh . rsh . shiftTo1
--   = (+1) . lsh . rsh . while even rsh
--   = (+1) . lsh . rsh . head . dropWhile even . iterate rsh
--   = (+1) . lsh . head . map rsh . dropWhile even . iterate rsh
--   = head . map ((+1) . lsh . rsh) . dropWhile even . iterate rsh

-- ... ?

f :: Integer -> Integer -> Integer
f n x = (2^(n-a) + b - 1) `div` 2
  where
    (a,b) = eo x

f' :: Integer -> Integer -> Integer
f' n x = 2^(n-k-1)*(2*c + 1)
  where
    (k,c) = msb x

-- eo x = (a,b) such that x = 2^a b  and b is odd.
eo :: Integer -> (Integer, Integer)
eo x
  | even x    = first (+1) (eo (x `div` 2))
  | otherwise = (0, x)

-- msb x = (k,c) such that x = 2^k + c and c < 2^k.
msb :: Integer -> (Integer, Integer)
msb x = (k, x - 2^k)
  where
    k = lg x

lg :: Integer -> Integer
lg 1 = 0
lg x = 1 + lg (x `div` 2)
