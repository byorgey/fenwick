open import Data.Nat
open import Data.Nat.Properties using (suc-injective)
open import Data.List

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)
open ≡-Reasoning

variable
  a : Set

data BT : Set → Set where
  Leaf   : (x : a) → BT a
  Branch : (x : a) → BT a → BT a → BT a

indBT : {P : BT a → Set} →
  ((x : a) → P (Leaf x)) →
  ((x : a) → (l r : BT a) → P l → P r → P (Branch x l r)) →
  (t : BT a) → P t
indBT lf br (Leaf x)       = lf x
indBT lf br (Branch x l r) = br x l r (indBT lf br l) (indBT lf br r)

recBT : {r : Set} → (a → r) → (a → r → r → r) → BT a → r
recBT {r = r} lf br = indBT {P = λ _ → r} lf (λ x _ _ r₁ r₂ → br x r₁ r₂)

∣_∣ : BT a → ℕ
∣_∣ = recBT (λ _ → 1) (λ _ l r → 1 + l + r)

data Bin : Set where
  𝟙     : Bin
  _×2   : Bin → Bin
  _×2+1 : Bin → Bin

ones : ℕ → ℕ
ones zero = 0
ones (suc n) = let z = ones n in 1 + z + z

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

bt : ℕ → Bin → BT Bin
bt zero    i = Leaf i
bt (suc n) i = Branch i (bt n (i ×2)) (bt n (i ×2+1))

btSize : (n : ℕ) → {b : Bin} → ∣ bt n b ∣ ≡ ones (suc n)
btSize zero    = refl
btSize (suc n) {b} =
  begin
  ∣ bt (suc n) b ∣
                                ≡⟨⟩
  ∣ Branch b (bt n _) (bt n _) ∣
                                ≡⟨⟩
  1 + ∣ bt n _ ∣ + ∣ bt n _ ∣
                                ≡⟨ cong (λ e → 1 + e + ∣ bt n _ ∣) (btSize n) ⟩
  1 + ones (suc n) + ∣ bt n _ ∣
                                ≡⟨ cong (λ e → 1 + ones (suc n) + e) (btSize n) ⟩
  1 + ones (suc n) + ones (suc n)
                                ≡⟨⟩
  ones (suc (suc n))
  ∎

inorder : BT a → List a
inorder (Leaf a)       = [ a ]
inorder (Branch a l r) = inorder l ++ [ a ] ++ inorder r

-- Need to generalize to interleaving where either |xs| = |ys| or |xs| = |ys|+1.

interleave : (xs : List a) → (ys : List a) → .(length xs ≡ length ys) → List a
interleave [] ys             _  = []
interleave (x ∷ xs) (y ∷ ys) pf = x ∷ y ∷ interleave xs ys (suc-injective pf)

length-drop : (n : ℕ) → (xs : List a) → length (drop n xs) ≡ length xs ∸ n
length-drop zero    xs       = refl
length-drop (suc n) []       = refl
length-drop (suc n) (x ∷ xs) = length-drop n xs

length-drop-eq : (n : ℕ) → (xs ys : List a) →
  length xs ≡ length ys → length (drop n xs) ≡ length (drop n ys)
length-drop-eq n xs ys eq rewrite length-drop n xs | length-drop n ys | eq = refl

length-take : (n : ℕ) → (xs : List a) → length (take n xs) ≡ n ⊓ length xs
length-take zero xs = refl
length-take (suc n) [] = refl
length-take (suc n) (x ∷ xs) = cong suc (length-take n xs)

length-take-eq : (n : ℕ) → (xs ys : List a) →
  length xs ≡ length ys → length (take n xs) ≡ length (take n ys)
length-take-eq n xs ys eq rewrite length-take n xs | length-take n ys | eq = refl

drop-interleave : (n : ℕ) → (xs ys : List a) → (eq : length xs ≡ length ys) →
  drop (double n) (interleave xs ys eq) ≡ interleave (drop n xs) (drop n ys) (length-drop-eq n xs ys eq)
drop-interleave zero xs ys eq = refl
drop-interleave (suc n) [] [] eq = refl
drop-interleave (suc n) (x ∷ xs) (y ∷ ys) eq = drop-interleave n xs ys (suc-injective eq)

take-interleave : (n : ℕ) → (xs ys : List a) → (eq : length xs ≡ length ys) →
  take (double n) (interleave xs ys eq) ≡ interleave (take n xs) (take n ys) (length-take-eq n xs ys eq)
take-interleave zero xs ys eq = refl
take-interleave (suc n) [] [] eq = refl
take-interleave (suc n) (x ∷ xs) (y ∷ ys) eq = cong (_∷_ x) (cong (_∷_ y) (take-interleave n xs ys (suc-injective eq)))
