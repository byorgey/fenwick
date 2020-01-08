open import Data.Bool using (Bool; true; false)
open import Data.Nat renaming (suc to S)
open import Data.Nat.Properties using (suc-injective; +-suc; _≤?_; n≤1+n; +-identityʳ; *-identityʳ)
open import Data.List
open import Data.List.Properties using (take++drop; length-applyUpTo)
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)

private
  variable
    a : Set

data BT : Set → Set where
  Empty  : BT a
  Branch : (x : a) → (l : BT a) → (r : BT a) → BT a

indBT : {P : BT a → Set} →
  P Empty →
  ((x : a) → (l r : BT a) → P l → P r → P (Branch x l r)) →
  (t : BT a) → P t
indBT z _  Empty          = z
indBT z br (Branch x l r) = br x l r (indBT z br l) (indBT z br r)

recBT : {r : Set} → r → (a → r → r → r) → BT a → r
recBT {r = r} z br = indBT {P = λ _ → r} z (λ x _ _ r₁ r₂ → br x r₁ r₂)

∣_∣ : BT a → ℕ
∣_∣ = recBT 0 (λ _ l r → 1 + l + r)

------------------------------------------------------------
-- Segment tree

-- value : BT a → a
-- value Empty = 0
-- value (Branch x _ _) = x

-- data IsSegTree : BT a → Set where
--   Empty  : IsSegTree Empty
--   Branch :   IsSegTree l

------------------------------------------------------------
-- Thinning
--
-- Need to put some Monoid/Group constraints around, and encode
-- segment tree properties...?  Would need this to e.g. prove recovery
-- of a full segment tree from a thinned version.

data Status : Set where
  Active : Status
  Inactive : Status

Hole : Status → Set → Set
Hole Active   a = a
Hole Inactive _ = ⊤

give : {s : Status} → a → Hole s a
give {s = Active}   x = x
give {s = Inactive} x = tt

data ThinnedR : Status → Set → Set where
  Empty  : {s : Status} → ThinnedR s a
  Branch : {s : Status} → Hole s a → ThinnedR Active a → ThinnedR Inactive a → ThinnedR s a

Thinned : Set → Set
Thinned = ThinnedR Active

thin : BT a → Thinned a
thin = thinR
  where
    thinR : {s : Status} → BT a → ThinnedR s a
    thinR Empty          = Empty
    thinR (Branch x l r) = Branch (give x) (thinR r) (thinR r)



------------------------------------------------------------

inorder : BT a → List a
inorder = recBT [] (λ x l r → l ++ [ x ] ++ r)

-- data Bin : Set where
--   𝟙   : Bin
--   _∷0 : Bin → Bin
--   _∷1 : Bin → Bin

2× : ℕ → ℕ
2× zero    = zero
2× (S n) = S (S (2× n))

2×-≤ : (m n : ℕ) → m ≤ n → 2× m ≤ 2× n
2×-≤ zero n m≤n = z≤n
2×-≤ (S m) (S n) (s≤s m≤n) = s≤s (s≤s (2×-≤ m n m≤n))

2×-+ : (n : ℕ) → 2× n ≡ n + n
2×-+ zero = refl
2×-+ (S n) rewrite (+-suc n n) = cong S (cong S (2×-+ n))

𝟙^_ : ℕ → ℕ
𝟙^ zero = 0
𝟙^ (S n) = S (2× (𝟙^ n))

𝟙^-≤ : (m n : ℕ) → m ≤ n → 𝟙^ m ≤ 𝟙^ n
𝟙^-≤ zero n m≤n = z≤n
𝟙^-≤ (S m) (S n) (s≤s m≤n) = s≤s (2×-≤ _ _ (𝟙^-≤ m n m≤n))

bt : ℕ → ℕ → BT ℕ
bt zero    _ = Empty
bt (S n) i = Branch i (bt n (2× i)) (bt n (S (2× i)))

btSize : (n : ℕ) → {b : ℕ} → ∣ bt n b ∣ ≡ 𝟙^ n
btSize zero = refl
btSize (S n) {b} rewrite (2×-+ (𝟙^ n)) | btSize n {2× b} | btSize n {S (2× b)}
  = refl

inorder′ : BT a → List a
inorder′ Empty          = []
inorder′ (Branch a l r) = inorder′ l ++ [ a ] ++ inorder′ r

inorder-correct : (t : BT a) → inorder t ≡ inorder′ t
inorder-correct Empty = refl
inorder-correct (Branch x l r) rewrite inorder-correct l | inorder-correct r = refl

------------------------------------------------------------

_⋎_ : (xs ys : List a) → List a
[] ⋎ _ = []
(x ∷ xs) ⋎ ys = x ∷ ys ⋎ xs

drop-⋎ : (n : ℕ) → (xs ys : List a) → (length xs ≡ length ys) →
  drop (2× n) (xs ⋎ ys) ≡ drop n xs ⋎ drop n ys
drop-⋎ zero xs ys eq = refl
drop-⋎ (S n) [] ys eq = refl
drop-⋎ (S n) (x ∷ xs) (y ∷ ys) eq = drop-⋎ n xs ys (suc-injective eq)

drop-++ : (n : ℕ) → (xs ys : List a) → length xs ≡ n → drop n (xs ++ ys) ≡ ys
drop-++ zero [] ys eq = refl
drop-++ (S n) (x ∷ xs) ys eq = drop-++ n xs ys (suc-injective eq)

take-⋎ : (n : ℕ) → (xs ys : List a) → (length xs ≡ length ys) →
  take (2× n) (xs ⋎ ys) ≡ take n xs ⋎ take n ys
take-⋎ zero xs ys eq = refl
take-⋎ (S n) [] ys eq = refl
take-⋎ (S n) (x ∷ xs) (y ∷ ys) eq = cong (_∷_ x) (cong (_∷_ y) (take-⋎ n xs ys (suc-injective eq)))

take-⋎′ : (n : ℕ) → (xs ys : List a) → (length xs ≡ S (length ys)) →
  take (S (2× n)) (xs ⋎ ys) ≡ take (S n) xs ⋎ take n ys
take-⋎′ n (x ∷ xs) ys eq = cong (_∷_ x) (take-⋎ n ys xs (suc-injective (sym eq)))

length-⋎ : (xs ys : List a) → (length xs ≡ length ys) → length (xs ⋎ ys) ≡ length xs + length ys
length-⋎ [] [] _ = refl
length-⋎ (x ∷ xs) (y ∷ ys) eq = begin
  length ((x ∷ xs) ⋎ (y ∷ ys))
                      ≡⟨⟩
  length (x ∷ y ∷ xs ⋎ ys)
                      ≡⟨⟩
  S (S (length (xs ⋎ ys)))
                      ≡⟨ cong S (cong S (length-⋎ xs ys (suc-injective eq))) ⟩
  S (S (length xs + length ys))
                      ≡⟨ cong S (sym (+-suc _ _)) ⟩
  S (length xs + S (length ys))
                      ≡⟨⟩
  S (length xs) + S (length ys)
                      ≡⟨⟩
  length (x ∷ xs) + length (y ∷ ys)
  ∎

⋎-++ : (xs₁ xs₂ ys₁ ys₂ : List a) → length xs₁ ≡ length xs₂ →
  (xs₁ ⋎ xs₂) ++ (ys₁ ⋎ ys₂) ≡ (xs₁ ++ ys₁) ⋎ (xs₂ ++ ys₂)
⋎-++ [] _ [] _ _ = refl
⋎-++ [] [] _ _ _ = refl
⋎-++ (x₁ ∷ xs₁) (x₂ ∷ xs₂) ys₁ ys₂ eq = cong (_∷_ x₁) (cong (_∷_ x₂) (⋎-++ xs₁ xs₂ ys₁ ys₂ (suc-injective eq)))

⋎-++′ : (xs₁ xs₂ ys₁ ys₂ : List a) → length xs₁ ≡ S (length xs₂) →
  (xs₁ ⋎ xs₂) ++ (ys₁ ⋎ ys₂) ≡ (xs₁ ++ ys₂) ⋎ (xs₂ ++ ys₁)
⋎-++′ (x ∷ xs₁) xs₂ ys₁ ys₂ eq = {!!}

------------------------------------------------------------

-- [1, 2, ..., 2^n - 1]
1⋯2^_ : ℕ → List ℕ
1⋯2^ n = applyUpTo S (𝟙^ n)

length-1⋯2^ : (n : ℕ) → length (1⋯2^ n) ≡ 𝟙^ n
length-1⋯2^ n = length-applyUpTo S _

-- [2^n, ..., 2^(n+1) - 1]
2⋯2^_ : ℕ → List ℕ
2⋯2^ n = drop (𝟙^ n) (1⋯2^ (S n))

take-applyUpTo : {A : Set} {f : ℕ → A} → (m n : ℕ) → m ≤ n → take m (applyUpTo f n) ≡ applyUpTo f m
take-applyUpTo zero n pf = refl
take-applyUpTo {f = f} (S m) (S n) (s≤s pf) = cong (_∷_ (f zero)) (take-applyUpTo m n pf)

take-1⋯2^ : (n : ℕ) → take (𝟙^ n) (1⋯2^ (S n)) ≡ (1⋯2^ n)
take-1⋯2^ n = take-applyUpTo (𝟙^ n) (S (2× (𝟙^ n))) (𝟙^-≤ n (S n) (n≤1+n n))

split-1⋯2^ : (n : ℕ) → 1⋯2^ (S n) ≡ (1⋯2^ n) ++ (2⋯2^ n)
split-1⋯2^ n = sym (begin
  (1⋯2^ n) ++ (2⋯2^ n)
                      ≡⟨⟩
  (1⋯2^ n) ++ drop (𝟙^ n) (1⋯2^ (S n))
                      ≡⟨ cong (λ s → s ++ drop (𝟙^ n) (1⋯2^ S n)) (sym (take-1⋯2^ n)) ⟩
  take (𝟙^ n) (1⋯2^ (S n)) ++ drop (𝟙^ n) (1⋯2^ S n)
                      ≡⟨ take++drop (𝟙^ n) (1⋯2^ S n) ⟩
  1⋯2^ (S n)
  ∎)

2^ : ℕ → ℕ
2^ zero = 1
2^ (S n) = 2× (2^ n)

-- interval i n = [i*2^n ... (i+1)*2^n - 1]
interval : ℕ → ℕ → List ℕ
interval i n = applyUpTo (_+_ (i * 2^ n)) (2^ n)

length-interval : (i n : ℕ) → length (interval i n) ≡ 2^ n
length-interval _ _ = length-applyUpTo _ _

------------------------------------------------------------

s : ℕ → List ℕ
s zero    = [ 0 ]
s (S n) = 0 ∷ (1⋯2^ S n) ⋎ s n

length-s : (n : ℕ) → length (s n) ≡ 𝟙^ (S n)
length-s zero = refl
length-s (S n) = begin
  length (s (S n))
                      ≡⟨⟩
  length (0 ∷ (1⋯2^ S n) ⋎ s n)
                      ≡⟨⟩
  S (length ((1⋯2^ S n) ⋎ s n))
                      ≡⟨ cong S (length-⋎ (1⋯2^ S n) (s n)
                         (trans (length-1⋯2^ _) (sym (length-s n))))
                       ⟩
  S (length (1⋯2^ S n) + length (s n))
                      ≡⟨ cong (λ r → S (r + length (s n))) (length-1⋯2^ _) ⟩
  S (𝟙^ (S n) + length (s n))
                      ≡⟨ cong (λ r → S (𝟙^ (S n) + r)) (length-s n) ⟩
  S (𝟙^ (S n) + 𝟙^ (S n))
                      ≡⟨ cong S (sym (2×-+ _)) ⟩
  S (2× (𝟙^ (S n)))
                      ≡⟨⟩
  𝟙^ (S (S n))
  ∎

length-s≡1⋯2^ : (n : ℕ) → length (s n) ≡ length (1⋯2^ S n)
length-s≡1⋯2^ n = trans (length-s n) (sym (length-1⋯2^ _))

s-prefix-∃ : (n : ℕ) → Σ[ ys ∈ List ℕ ] (s (S n) ≡ s n ++ ys)
s-prefix-∃ zero = 1 ∷ zero ∷ [] , refl
s-prefix-∃ (S n) with s-prefix-∃ n
... | (ys′ , eq) = ((2⋯2^ S n) ⋎ ys′) ,
  (begin
    s (S (S n))
                      ≡⟨⟩
    0 ∷ (1⋯2^ S (S n)) ⋎ s (S n)
                      ≡⟨ cong (λ r → 0 ∷ ((1⋯2^ S (S n)) ⋎ r)) eq ⟩
    0 ∷ (1⋯2^ S (S n)) ⋎ (s n ++ ys′)
                      ≡⟨ cong (λ r → 0 ∷ (r ⋎ (s n ++ ys′))) (split-1⋯2^ (S n)) ⟩
    0 ∷ ((1⋯2^ S n) ++ (2⋯2^ S n)) ⋎ (s n ++ ys′)
                      ≡⟨ cong (_∷_ 0) (sym (⋎-++ (1⋯2^ S n) _ _ _ (sym (length-s≡1⋯2^ n)))) ⟩
    0 ∷ ((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ ys′)
                      ≡⟨⟩
    (0 ∷ (1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ ys′)
                      ≡⟨⟩
    s (S n) ++ ((2⋯2^ S n) ⋎ ys′)
  ∎)

P : ℕ → List ℕ
P n = drop (𝟙^ n) (s n)

mutual
  s-prefix : (n : ℕ) → s (S n) ≡ s n ++ P (S n)
  s-prefix 0 = refl
  s-prefix (S n) = begin
    s (S (S n))
                        ≡⟨⟩
    0 ∷ (1⋯2^ S (S n)) ⋎ s (S n)
                        ≡⟨ cong (λ r → 0 ∷ ((1⋯2^ S (S n)) ⋎ r)) (s-prefix n) ⟩
    0 ∷ (1⋯2^ S (S n)) ⋎ (s n ++ P (S n))
                        ≡⟨ cong (λ r → 0 ∷ (r ⋎ (s n ++ P (S n))))
                                (split-1⋯2^ (S n))
                         ⟩
    0 ∷ ((1⋯2^ S n) ++ (2⋯2^ S n)) ⋎ (s n ++ P (S n))
                        ≡⟨ cong (_∷_ 0) (sym (⋎-++ (1⋯2^ S n) _ _ _ (sym (length-s≡1⋯2^ n)))) ⟩
    0 ∷ ((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n))
                        ≡⟨⟩
    (0 ∷ (1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n))
                        ≡⟨⟩
    s (S n) ++ ((2⋯2^ S n) ⋎ P (S n))
                        ≡⟨ cong (λ r → s (S n) ++ r) (sym (P-merge (S n))) ⟩
    s (S n) ++ P (S (S n))
    ∎

  P-merge : (n : ℕ) → P (S n) ≡ (2⋯2^ n) ⋎ P n
  P-merge zero    = refl
  P-merge (S n) = begin
    P (S (S n))
                        ≡⟨⟩
    drop (𝟙^ S (S n)) (s (S (S n)))
                        ≡⟨⟩
    drop (𝟙^ S (S n)) (0 ∷ (1⋯2^ S (S n)) ⋎ s (S n))
                        ≡⟨⟩
    drop (2× (𝟙^ S n)) ((1⋯2^ S (S n)) ⋎ s (S n))
                        ≡⟨ cong (λ r → drop (2× (𝟙^ S n)) (r ⋎ s (S n))) (split-1⋯2^ (S n)) ⟩
    drop (2× (𝟙^ S n)) (((1⋯2^ S n) ++ (2⋯2^ S n)) ⋎ s (S n))
                        ≡⟨ cong
                             (λ r →
                                drop (2× (𝟙^ S n)) (((1⋯2^ S n) ++ (2⋯2^ S n)) ⋎ r))
                             (s-prefix n) ⟩
    drop (2× (𝟙^ S n)) (((1⋯2^ S n) ++ (2⋯2^ S n)) ⋎ (s n ++ P (S n)))
                        ≡⟨ cong (drop (2× (𝟙^ S n)))
                             (sym (⋎-++ (1⋯2^ S n) (s n) _ _ (sym (length-s≡1⋯2^ n)))) ⟩
    drop (2× (𝟙^ S n)) (((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n)))
                        ≡⟨ cong (λ r → drop r (((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n))))
                             (2×-+ (𝟙^ S n)) ⟩
    drop ((𝟙^ S n) + (𝟙^ S n)) (((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n)))
                        ≡⟨ cong
                             (λ r →
                                drop (r + (𝟙^ S n))
                                (((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n))))
                             (sym (length-1⋯2^ (S n))) ⟩
    drop (length (1⋯2^ S n) + (𝟙^ S n)) (((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n)))
                        ≡⟨ cong
                             (λ r →
                                drop (length (1⋯2^ S n) + r)
                                (((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n))))
                             (sym (length-s n)) ⟩
    drop (length (1⋯2^ S n) + length (s n)) (((1⋯2^ S n) ⋎ s n) ++ ((2⋯2^ S n) ⋎ P (S n)))
                        ≡⟨ drop-++ ((length (1⋯2^ S n) + length (s n))) ((1⋯2^ S n) ⋎ s n) _
                             (length-⋎ (1⋯2^ S n) (s n) (sym (length-s≡1⋯2^ n))) ⟩
    (2⋯2^ S n) ⋎ P (S n)
    ∎

    -- WHEW!

inorder-bt-merge : (n i : ℕ) → inorder (bt (S n) i) ≡ interval i n ⋎ inorder (bt n i)
inorder-bt-merge zero i rewrite +-identityʳ (i * 1) | *-identityʳ i = refl
inorder-bt-merge (S n) i = begin
  inorder (bt (S (S n)) i)
                      ≡⟨⟩
  inorder (Branch i (bt (S n) (2× i)) (bt (S n) (S (2× i))))
                      ≡⟨⟩
  inorder (bt (S n) (2× i)) ++ [ i ] ++ inorder (bt (S n) (S (2× i)))
                      ≡⟨ cong (λ r → r ++ [ i ] ++ inorder (bt (S n) (S (2× i))))
                           (inorder-bt-merge n _) ⟩
  (interval (2× i) n ⋎ inorder (bt n (2× i))) ++ [ i ] ++ inorder (bt (S n) (S (2× i)))
                      ≡⟨ cong (λ r → (interval (2× i) n ⋎ inorder (bt n (2× i))) ++ [ i ] ++ r)
                           (inorder-bt-merge n _) ⟩
  (interval (2× i) n ⋎ inorder (bt n (2× i))) ++ [ i ] ++ (interval (S (2× i)) n ⋎ inorder (bt n (S (2× i))))
                      ≡⟨ {!!} ⟩
  interval i (S n) ⋎ inorder (bt (S n) i)
  ∎

-- inorder-bt-merge zero _ = refl
-- inorder-bt-merge (S n) = begin
--   inorder (bt (S (S n)) i)
--                       ≡⟨⟩
--   inorder (Branch 1 (bt (S n) (2× 1)) (bt (S n) (S (2× 1))))
--                       ≡⟨⟩
--   inorder (bt (S n) (2× 1)) ++ [ 1 ] ++ inorder (bt (S n) (S (2× 1)))
--                       ≡⟨ {!!} ⟩
--   (2⋯2^ S n) ⋎ inorder (bt (S n) 1)
--   ∎

-- bt : ℕ → ℕ → BT ℕ
-- bt zero    _ = Empty
-- bt (S n) i = Branch i (bt n (2× i)) (bt n (S (2× i)))


-- Need to generalize...
inorder-bt : (n : ℕ) → P n ≡ inorder (bt n 1) ++ [ 0 ]
inorder-bt n = {!!}


-- inorder-bt-gen : (n i ∶ ℕ) → inorder (bt n i) ≡ interleave

-- inorder-bt zero    = refl
-- inorder-bt (S n) = sym (begin
--   inorder (bt (S n) 1) ++ [ 0 ]
--                       ≡⟨⟩
--   inorder (Branch 1 (bt n 2) (bt n 3)) ++ [ 0 ]
--                       ≡⟨⟩
--   (inorder (bt n 2) ++ [ 1 ] ++ inorder (bt n 3)) ++ [ 0 ]
--                       ≡⟨ {!!} ⟩ -- Can't use IH here.
--   P (S n)
--   ∎)


-- inorder (bt 3 (2× ∘ S)) =
--   8 ∷ 4 ∷ 9 ∷ 2 ∷ 10 ∷ 5 ∷ 11 ∷ []
--
-- P 2 =
--   2 ∷ 1 ∷ 3 ∷ 0 ∷ []
--   10 ∷ 01 ∷ 11
-- P 3 =
--   4 ∷ 2 ∷ 5 ∷ 1 ∷ 6 ∷ 3 ∷ 7 ∷ 0 ∷ []
--   100 ∷ 010 ∷ 101 ∷ 001 ∷ 110 ∷ 011 ∷ 111

