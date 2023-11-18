{-# OPTIONS --cubical #-}

-- open import Cubical.Core.Everything

open import Data.Bool
open import Relation.Binary.PropositionalEquality

data Bit : Set where
  O : Bit
  I : Bit

data Bits : Set where
  zeros : Bits
  ones : Bits
  _∷_ : Bit → Bits → Bits

  zz : O ∷ zeros ≡ zeros
  oo : I ∷ ones ≡ ones
