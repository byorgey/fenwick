open import Data.Nat
open import Data.List

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data BT : Set → Set where
  Leaf   : {A : Set} → (a : A) → BT A
  Branch : {A : Set} → (a : A) → BT A → BT A → BT A

data Bin : Set where
  𝟙     : Bin
  _×2   : Bin → Bin
  _×2+1 : Bin → Bin

bt : ℕ → Bin → BT Bin
bt zero    i = Leaf i
bt (suc n) i = Branch i (bt n (i ×2)) (bt n (i ×2+1))

inorder : {A : Set} → BT A → List A
inorder (Leaf a)       = [ a ]
inorder (Branch a l r) = inorder l ++ [ a ] ++ inorder r

interleave : {A : Set} → List A → List A → List A
interleave []       _  = []
interleave (x ∷ xs) ys = x ∷ interleave ys xs

