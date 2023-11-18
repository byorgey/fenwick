{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Relation.Binary.PropositionalEquality

record Bits : Set where
  coinductive
  constructor _∷_
  field
    hd : Bool
    tl : Bits

open Bits

repeat : Bool → Bits
hd (repeat b) = b
tl (repeat b) = repeat b

record _≈_ (xs : Bits) (ys : Bits) : Set where
  coinductive
  field
    hd-≡ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

open _≈_

𝟘 : Bool
𝟘 = false

𝟙 : Bool
𝟙 = true

zeros : Bits
zeros = repeat 𝟘

ones : Bits
ones = repeat 𝟙

map : (Bool → Bool) → (Bits → Bits)
hd (map f bs) = f (hd bs)
tl (map f bs) = map f (tl bs)

zipWith : (Bool → Bool → Bool) → Bits → Bits → Bits
hd (zipWith f xs ys) = f (hd xs) (hd ys)
tl (zipWith f xs ys) = zipWith f (tl xs) (tl ys)

_&_ : Bits → Bits → Bits
_&_ = zipWith _∧_

inc : Bits → Bits
hd (inc bs) = not (hd bs)
tl (inc bs) with hd bs
... | false = bs
... | true = inc bs

infix 30 _+_
_+_ : Bits → Bits → Bits
hd (x + y) = hd x xor hd y
tl (x + y) with hd x ∧ hd y
... | false = tl x + tl y
... | true = tl x + inc (tl y)

LSB : Bits → Bits
hd (LSB bs) = hd bs
tl (LSB bs) with hd bs
... | false = LSB (tl bs)
... | true = repeat 𝟘

negate : Bits → Bits
negate bs = inc (map not bs)

hd-negate : (x : Bits) → (hd x ≡ hd (negate x))
hd-negate x with hd x
... | false = refl
... | true = refl

negate-inv : (x : Bits) → (x + negate x ≈ zeros)
hd-≡ (negate-inv x) = {!!}
tl-≈ (negate-inv x) = {!!}
