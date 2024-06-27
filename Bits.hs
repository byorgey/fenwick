{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

import Control.Category ((>>>))
import Prelude hiding (zipWith, even, odd)

data CStream a = Rep a | Snoc (CStream a) a
  deriving (Functor)

expand :: CStream a -> CStream a
expand (Rep a) = Snoc (Rep a) a
expand as = as

pattern (:::) :: Eq a => CStream a -> a -> CStream a
pattern (:::) as a <- (expand -> Snoc as a)
  where
    Rep a ::: b | a == b = Rep a
    as ::: a = Snoc as a

instance Eq a => Eq (CStream a) where
  Rep a == Rep b = a == b
  (as ::: a) == (bs ::: b) = a == b && as == bs

zipWith :: (Eq a, Eq b, Eq c) => (a -> b -> c) -> CStream a -> CStream b -> CStream c
zipWith f (Rep a) (Rep b) = Rep (f a b)
zipWith f (as ::: a) (bs ::: b) = zipWith f as bs ::: f a b

infix 4 ===
(===) :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
f === g = \a -> f a == g a

-- instance Show a => Show (CStream a) where
--   show (Rep a) = "... ::: " ++ show a
--   show (as ::: a) = show as ++ " ::: " ++ show a

------------------------------------------------------------

type Bits = CStream Bit

data Bit = O | I  deriving (Eq, Ord, Show, Enum)

inv :: Bit -> Bit
inv O = I
inv I = O

(.&.) :: Bit -> Bit -> Bit
O .&. _ = O
I .&. b = b

(.|.) :: Bit -> Bit -> Bit
I .|. _ = I
O .|. b = b

pattern Zeros = Rep O
pattern Ones = Rep I

toBits :: Int -> Bits
toBits n
  | n == 0 = Zeros
  | n < 0 = neg (toBits (-n))
  | otherwise  = toBits (n `div` 2) ::: toEnum (n `mod` 2)

instance Show Bits where
  show Zeros = "0"
  show bs = reverse . go $ bs
   where
    go Zeros = ""
    go Ones = "1..."
    go (bs ::: b) = showBit b : go bs

    showBit = ("01"!!) . fromEnum

instance Num Bits where
  fromInteger = toBits . fromInteger
  (+) = (.+.)
  negate = neg

fromBits :: Bits -> Int
fromBits Zeros = 0
fromBits Ones = -1
fromBits (bs ::: b) = 2 * fromBits bs + fromEnum b

inc :: Bits -> Bits
inc Ones = Zeros
inc (bs ::: O) = bs ::: I
inc (bs ::: I) = inc bs ::: O

dec :: Bits -> Bits
dec Zeros = Ones
dec (bs ::: I) = bs ::: O
dec (bs ::: O) = dec bs ::: I

lsb :: Bits -> Bits
lsb (bs ::: O) = lsb bs ::: O
lsb (_ ::: I) = Zeros ::: I

(.+.) :: Bits -> Bits -> Bits
xs .+. Zeros = xs
Zeros .+. ys = ys
Ones .+. Ones = Ones ::: O
(xs ::: I) .+. (ys ::: I)  = inc (xs .+. ys) ::: O
(xs ::: x) .+. (ys ::: y)  = (xs .+. ys) ::: (x .|. y)

(.&&.) :: Bits -> Bits -> Bits
(.&&.) = zipWith (.&.)

neg :: Bits -> Bits
neg = inc . fmap inv

setTo :: Bit -> Int -> Bits -> Bits
setTo b' 0 (bs ::: _) = bs ::: b'
setTo b' k (bs ::: b) = setTo b' (k-1) bs ::: b

set, clear :: Int -> Bits -> Bits
set = setTo I
clear = setTo O

test :: Int -> Bits -> Bool
test 0 (bs ::: b) = b == I
test n (bs ::: _) = test (n-1) bs

even, odd :: Bits -> Bool
odd = test 0
even = not . odd

shr :: Bits -> Bits
shr (bs ::: _) = bs

shl :: Bits -> Bits
shl bs = bs ::: O

while :: (a -> Bool) -> (a -> a) -> a -> a
while p f = head . dropWhile p . iterate f


class Exponentiable a where
  pow :: a -> Int -> a

instance Exponentiable Int where
  pow = (^)

instance Exponentiable (a -> a) where
  pow _ 0 = id
  pow f k = pow f (k-1) . f


interleave :: [a] -> [a] -> [a]
[] `interleave` _ = []
(x : xs) `interleave` ys = x : (ys `interleave` xs)

b :: Int -> [Int] --- return [Bits]??
b 0 = [2]
b n = map (2*) [pow 2 n .. pow 2 n + pow 2 (n-1) - 1] `interleave` b (n-1)

f2b n k = b n ! k

(a : _) ! 1 = a
(_ : as) ! k = as ! (k-1)

f2b' :: Int -> Bits -> Bits
f2b' n = dec . while even shr . set (n+1)


b2f' :: Int -> Bits -> Bits
b2f' n = clear (n+1) . while (not . test (n+1)) shl . inc

activeParentBinary :: Bits -> Bits
activeParentBinary = while odd shr . shr

onOdd :: (Bits -> Bits) -> Bits -> Bits
onOdd f (bs ::: O) = onOdd f bs ::: O
onOdd f bs = f bs

prevSegmentBinary :: Bits -> Bits
prevSegmentBinary = dec . while even shr
