open import Data.Bool using (Bool; true; false)
open import Data.Nat renaming (suc to 1+)
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties using (take++drop; length-applyUpTo; ++-assoc; length-++)
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

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
2× (1+ n) = 1+ (1+ (2× n))

2×-≤ : (m n : ℕ) → m ≤ n → 2× m ≤ 2× n
2×-≤ zero n m≤n = z≤n
2×-≤ (1+ m) (1+ n) (s≤s m≤n) = s≤s (s≤s (2×-≤ m n m≤n))

2×-+ : (n : ℕ) → 2× n ≡ n + n
2×-+ zero = refl
2×-+ (1+ n) rewrite (+-suc n n) = cong 1+ (cong 1+ (2×-+ n))

*-2× : (a b : ℕ) → a * 2× b ≡ 2× a * b
*-2× zero b = refl
*-2× (1+ a) b = begin
  2× b + a * 2× b

    ≡⟨ cong₂ _+_ (2×-+ b) refl ⟩

  b + b + a * 2× b

    ≡⟨ +-assoc b b (a * 2× b) ⟩

  b + (b + a * 2× b)

    ≡⟨ cong (_+_ b) (cong (_+_ b) (*-2× a b)) ⟩

  b + (b + 2× a * b) ∎

*-1+2× : (a b : ℕ) → a * 1+ (2× b) ≡ 2× a * b + a
*-1+2× a b = begin
  a * 1+ (2× b)

    ≡⟨ *-comm a _ ⟩

  a + 2× b * a

    ≡⟨ cong (_+_ a) (sym (*-2× b a)) ⟩

  a + b * 2× a

    ≡⟨ cong (_+_ a) (*-comm b _) ⟩

  a + 2× a * b

    ≡⟨ +-comm a _ ⟩

  2× a * b + a ∎

2^ : ℕ → ℕ
2^ zero = 1
2^ (1+ n) = 2× (2^ n)

𝟙^_ : ℕ → ℕ
𝟙^ zero = 0
𝟙^ (1+ n) = 1+ (2× (𝟙^ n))

𝟙^-≤ : (m n : ℕ) → m ≤ n → 𝟙^ m ≤ 𝟙^ n
𝟙^-≤ zero n m≤n = z≤n
𝟙^-≤ (1+ m) (1+ n) (s≤s m≤n) = s≤s (2×-≤ _ _ (𝟙^-≤ m n m≤n))

1+𝟙^ : (n : ℕ) → 1+ (𝟙^ n) ≡ 2^ n
1+𝟙^ zero = refl
1+𝟙^ (1+ n) = cong 2× (1+𝟙^ n)

split-𝟙^ : (n : ℕ) → (𝟙^ (1+ n)) ≡ 𝟙^ n + 2^ n
split-𝟙^ n = begin
  𝟙^ (1+ n)

    ≡⟨⟩

  1+ (2× (𝟙^ n))

    ≡⟨ cong 1+ (2×-+ _) ⟩

  1+ (𝟙^ n + 𝟙^ n)

    ≡⟨ sym (+-suc _ _) ⟩

  𝟙^ n + 1+ (𝟙^ n)

    ≡⟨ cong₂ _+_ refl (1+𝟙^ _) ⟩

  𝟙^ n + 2^ n ∎

bt : ℕ → ℕ → BT ℕ
bt zero    _ = Empty
bt (1+ n) i = Branch i (bt n (2× i)) (bt n (1+ (2× i)))

btSize : (n : ℕ) → {b : ℕ} → ∣ bt n b ∣ ≡ 𝟙^ n
btSize zero = refl
btSize (1+ n) {b} rewrite (2×-+ (𝟙^ n)) | btSize n {2× b} | btSize n {1+ (2× b)}
  = refl

inorder′ : BT a → List a
inorder′ Empty          = []
inorder′ (Branch a l r) = inorder′ l ++ [ a ] ++ inorder′ r

inorder-correct : (t : BT a) → inorder t ≡ inorder′ t
inorder-correct Empty = refl
inorder-correct (Branch x l r) rewrite inorder-correct l | inorder-correct r = refl

length-inorder : (t : BT a) → length (inorder t) ≡ ∣ t ∣
length-inorder Empty          = refl
length-inorder (Branch x l r) = begin
  length (inorder (Branch x l r))

    ≡⟨⟩

  length (inorder l ++ [ x ] ++ inorder r)

    ≡⟨ length-++ (inorder l) ⟩

  length (inorder l) + length ([ x ] ++ inorder r)

    ≡⟨ cong₂ _+_ refl (length-++ [ x ] {inorder r}) ⟩

  length (inorder l) + (length [ x ] + length (inorder r))

    ≡⟨ cong₂ _+_ (length-inorder l) (cong₂ _+_ refl (length-inorder r)) ⟩

  ∣ l ∣ + (1 + ∣ r ∣)

    ≡⟨ sym (+-assoc ∣ l ∣ _ _) ⟩

  (∣ l ∣ + 1) + ∣ r ∣

    ≡⟨ cong₂ _+_ (+-comm ∣ l ∣ _) refl ⟩

  1+ (∣ l ∣ + ∣ r ∣)

    ≡⟨⟩

  ∣ Branch x l r ∣ ∎

------------------------------------------------------------

_⋎_ : (xs ys : List a) → List a
[] ⋎ _ = []
(x ∷ xs) ⋎ ys = x ∷ ys ⋎ xs

drop-⋎ : (n : ℕ) → (xs ys : List a) → (length xs ≡ length ys) →
  drop (2× n) (xs ⋎ ys) ≡ drop n xs ⋎ drop n ys
drop-⋎ zero xs ys eq = refl
drop-⋎ (1+ n) [] ys eq = refl
drop-⋎ (1+ n) (x ∷ xs) (y ∷ ys) eq = drop-⋎ n xs ys (suc-injective eq)

drop-++ : (n : ℕ) → (xs ys : List a) → length xs ≡ n → drop n (xs ++ ys) ≡ ys
drop-++ zero [] ys eq = refl
drop-++ (1+ n) (x ∷ xs) ys eq = drop-++ n xs ys (suc-injective eq)

take₀-⋎ : (n : ℕ) → (xs ys : List a) → (length xs ≡ length ys) →
  take (2× n) (xs ⋎ ys) ≡ take n xs ⋎ take n ys
take₀-⋎ zero xs ys eq = refl
take₀-⋎ (1+ n) [] ys eq = refl
take₀-⋎ (1+ n) (x ∷ xs) (y ∷ ys) eq = cong (_∷_ x) (cong (_∷_ y) (take₀-⋎ n xs ys (suc-injective eq)))

take₁-⋎ : (n : ℕ) → (xs ys : List a) → (length xs ≡ 1+ (length ys)) →
  take (1+ (2× n)) (xs ⋎ ys) ≡ take (1+ n) xs ⋎ take n ys
take₁-⋎ n (x ∷ xs) ys eq = cong (_∷_ x) (take₀-⋎ n ys xs (suc-injective (sym eq)))

length-⋎ : (xs ys : List a) → (length xs ≡ length ys) → length (xs ⋎ ys) ≡ length xs + length ys
length-⋎ [] [] _ = refl
length-⋎ (x ∷ xs) (y ∷ ys) eq = begin
  length ((x ∷ xs) ⋎ (y ∷ ys))

    ≡⟨⟩

  length (x ∷ y ∷ xs ⋎ ys)

    ≡⟨⟩

  1+ (1+ (length (xs ⋎ ys)))

    ≡⟨ cong 1+ (cong 1+ (length-⋎ xs ys (suc-injective eq))) ⟩

  1+ (1+ (length xs + length ys))

    ≡⟨ cong 1+ (sym (+-suc _ _)) ⟩

  1+ (length xs + 1+ (length ys))

    ≡⟨⟩

  1+ (length xs) + 1+ (length ys)

    ≡⟨⟩

  length (x ∷ xs) + length (y ∷ ys) ∎

⋎-++₀ : (xs₁ xs₂ ys₁ ys₂ : List a) → length xs₁ ≡ length xs₂ →
  (xs₁ ⋎ xs₂) ++ (ys₁ ⋎ ys₂) ≡ (xs₁ ++ ys₁) ⋎ (xs₂ ++ ys₂)
⋎-++₀ [] _ [] _ _ = refl
⋎-++₀ [] [] _ _ _ = refl
⋎-++₀ (x₁ ∷ xs₁) (x₂ ∷ xs₂) ys₁ ys₂ eq = cong (_∷_ x₁) (cong (_∷_ x₂) (⋎-++₀ xs₁ xs₂ ys₁ ys₂ (suc-injective eq)))

⋎-++₁ : (xs₁ xs₂ ys₁ ys₂ : List a) → length xs₁ ≡ 1+ (length xs₂) →
  (xs₁ ⋎ xs₂) ++ (ys₁ ⋎ ys₂) ≡ (xs₁ ++ ys₂) ⋎ (xs₂ ++ ys₁)
⋎-++₁ (x₁ ∷ xs₁) xs₂ ys₁ ys₂ eq = cong (_∷_ x₁) (⋎-++₀ xs₂ xs₁ ys₁ ys₂ (suc-injective (sym eq)))

⋎-snoc₀ : (xs ys : List a) → (z : a) → (length xs ≡ length ys) →
  (xs ⋎ ys) ++ [ z ] ≡ (xs ++ [ z ]) ⋎ ys
⋎-snoc₀ [] [] _ _ = refl
⋎-snoc₀ (x ∷ xs) (y ∷ ys) z eq
  = cong (_∷_ x) (cong (_∷_ y) (⋎-snoc₀ _ _ _ (suc-injective eq)))

⋎-snoc₁ : (xs ys : List a) → (z : a) → (length xs ≡ 1+ (length ys)) →
  (xs ⋎ ys) ++ [ z ] ≡ xs ⋎ (ys ++ [ z ])
⋎-snoc₁ (x ∷ xs) ys z eq = cong (_∷_ x) (⋎-snoc₀ _ _ _ (suc-injective (sym eq)))

------------------------------------------------------------

-- [1, 2, ..., 2^n - 1]
1⋯2^_ : ℕ → List ℕ
1⋯2^ n = applyUpTo 1+ (𝟙^ n)

length-1⋯2^ : (n : ℕ) → length (1⋯2^ n) ≡ 𝟙^ n
length-1⋯2^ n = length-applyUpTo 1+ _

-- [2^n, ..., 2^(n+1) - 1]
2^_⋯2^_ : (n m : ℕ) → {{pf : m ≡ 1+ n}} → List ℕ
2^ n ⋯2^ _ = drop (𝟙^ n) (1⋯2^ (1+ n))

take-applyUpTo : {A : Set} {f : ℕ → A} → (m n : ℕ) → m ≤ n → take m (applyUpTo f n) ≡ applyUpTo f m
take-applyUpTo zero n pf = refl
take-applyUpTo {f = f} (1+ m) (1+ n) (s≤s pf) = cong (_∷_ (f zero)) (take-applyUpTo m n pf)

take-1⋯2^ : (n : ℕ) → take (𝟙^ n) (1⋯2^ (1+ n)) ≡ (1⋯2^ n)
take-1⋯2^ n = take-applyUpTo (𝟙^ n) (1+ (2× (𝟙^ n))) (𝟙^-≤ n (1+ n) (n≤1+n n))

split-1⋯2^ : (n : ℕ) → 1⋯2^ (1+ n) ≡ (1⋯2^ n) ++ (2^ n ⋯2^ (1+ n))
split-1⋯2^ n = sym (begin

  (1⋯2^ n) ++ (2^ n ⋯2^ (1+ n))

    ≡⟨⟩

  (1⋯2^ n) ++ drop (𝟙^ n) (1⋯2^ (1+ n))

    ≡⟨ cong₂ _++_ (sym (take-1⋯2^ n)) refl ⟩

  take (𝟙^ n) (1⋯2^ (1+ n)) ++ drop (𝟙^ n) (1⋯2^ (1+ n))

    ≡⟨ take++drop (𝟙^ n) (1⋯2^ (1+ n)) ⟩

  1⋯2^ (1+ n) ∎)

-- Is this in the stdlib??
drop-drop : {A : Set} → (m n : ℕ) → (xs : List A) → drop m (drop n xs) ≡ drop (m + n) xs
drop-drop zero n xs = refl
drop-drop (1+ m) zero [] = refl
drop-drop (1+ m) (1+ n) [] = refl
drop-drop (1+ m) zero (x ∷ xs) rewrite +-identityʳ m = refl
drop-drop (1+ m) (1+ n) (x ∷ xs) rewrite +-suc m n = drop-drop (1+ m) n xs

-- This *is* in the stdlib but using ∸ instead of the side condition
-- about length.  I find this formulation easier to work with.
length-drop : {A : Set} → (m n : ℕ) → (xs : List A) → (length xs ≡ m + n) → length (drop m xs) ≡ n
length-drop zero n [] eq = eq
length-drop zero n (x ∷ xs) eq = eq
length-drop (1+ m) n (x ∷ xs) eq = length-drop m n xs (suc-injective eq)

length-2^⋯2^ : (n : ℕ) → length (2^ n ⋯2^ (1+ n)) ≡ 2^ n
length-2^⋯2^ n = begin
  length (2^ n ⋯2^ (1+ n))

    ≡⟨⟩

  length (drop (𝟙^ n) (1⋯2^ (1+ n)))

    ≡⟨ length-drop (𝟙^ n) (2^ n) (1⋯2^ (1+ n)) (trans (length-1⋯2^ (1+ n)) (split-𝟙^ n)) ⟩

  2^ n ∎

-- interval i n = [i*2^n ... (i+1)*2^n - 1]
interval : ℕ → ℕ → List ℕ
interval i n = applyUpTo (_+_ (2^ n * i)) (2^ n)

length-interval : (i n : ℕ) → length (interval i n) ≡ 2^ n
length-interval _ _ = length-applyUpTo _ _

applyUpTo-≡ : {A : Set} → (f g : ℕ → A) → (n : ℕ) →
  ((k : ℕ) → (k < n) → f k ≡ g k) → applyUpTo f n ≡ applyUpTo g n
applyUpTo-≡ f g zero eq = refl
applyUpTo-≡ f g (1+ n) eq = cong₂ _∷_ (eq _ (s≤s z≤n)) (applyUpTo-≡ (f ∘ 1+) (g ∘ 1+) n
                                                         (λ k pf → eq (1+ k) (s≤s pf)))

applyUpTo-++ : {A : Set} → (f g h : ℕ → A) → (n m l : ℕ) →
  ((k : ℕ) → (k < n) → f k ≡ h k) →
  ((k : ℕ) → (k < m) → g k ≡ h (n + k)) →
  (n + m ≡ l) → applyUpTo f n ++ applyUpTo g m ≡ applyUpTo h l
applyUpTo-++ f g h zero m l feq geq n+m≡l rewrite n+m≡l = applyUpTo-≡ g h l geq
applyUpTo-++ f g h (1+ n) m (1+ l) feq geq n+m≡l =
  cong₂ _∷_ (feq _ (s≤s z≤n)) (applyUpTo-++ (f ∘ 1+) g (h ∘ 1+) n _ _ (λ k z → feq (1+ k) (s≤s z)) geq (suc-injective n+m≡l))

-- Ugh, is there a prettier way to do the case analysis here?
drop-applyUpTo : {A : Set} → (f g : ℕ → A) → (k m n : ℕ) →
  (k + n ≡ m) →
  ((x : ℕ) → f (k + x) ≡ g x) →
  drop k (applyUpTo f m) ≡ applyUpTo g n
drop-applyUpTo f g zero zero zero k+n≡m f≡g = refl
drop-applyUpTo f g zero zero (1+ n) () f≡g
drop-applyUpTo f g (1+ k) zero (1+ n) () f≡g
drop-applyUpTo f g zero (1+ m) (1+ .m) refl f≡g =
  cong₂ _∷_ (f≡g zero) (applyUpTo-≡ (f ∘ 1+) (g ∘ 1+) m (λ k _ → f≡g (1+ k)))
drop-applyUpTo f g (1+ k) (1+ m) n k+n≡m f≡g = drop-applyUpTo (f ∘ 1+) g k m n (suc-injective k+n≡m) f≡g

-- [2i*2^n ... (2i+1)*2^n - 1] ++ [(2i+1)*2^n ... (2i+2)*2^n - 1] = [i*2^{n+1} ... (i+1)*2^{n+1}-1]
interval-++ : (n i : ℕ) → interval (2× i) n ++ interval (1+ (2× i)) n ≡ interval i (1+ n)
interval-++ zero i
  rewrite +-identityʳ (2× i) | +-identityʳ (2× i) | +-identityʳ i | +-identityʳ (i + i)
        | 2×-+ i | sym (+-comm (i + i) 1) = refl
interval-++ (1+ n) i =
  applyUpTo-++ (_+_ (2^ (1+ n) * 2× i)) (_+_ (2^ (1+ n) * 1+ (2× i))) _
    (2^ (1+ n)) _ _ lemma₁ lemma₂ (sym (2×-+ _))

  where
    lemma₁ : (k : ℕ) → k < 2× (2^ n) → 2× (2^ n) * 2× i + k ≡ 2× (2× (2^ n)) * i + k
    lemma₁ k _ = cong₂ _+_ (*-2× (2× (2^ n)) i) refl

    lemma₂ : (k : ℕ) → k < 2× (2^ n) → 2× (2^ n) * 1+ (2× i) + k ≡ 2× (2× (2^ n)) * i + (2× (2^ n) + k)
    lemma₂ k _ rewrite (sym (+-assoc (2^ (1+ (1+ n)) * i) (2^ (1+ n)) k)) =
      cong₂ _+_ (*-1+2× (2^ (1+ n)) i) refl


2⋯2^≡interval : (n : ℕ) → 2^ n ⋯2^ (1+ n) ≡ interval 1 n
2⋯2^≡interval zero = refl
2⋯2^≡interval (1+ n) = begin
  2^ (1+ n) ⋯2^ (1+ (1+ n))

    ≡⟨⟩

  drop (𝟙^ (1+ n)) (1⋯2^ (1+ (1+ n)))

    ≡⟨ drop-applyUpTo (1+ ∘ 1+) _ (2× (𝟙^ n)) _ _ lemma₁ lemma₂ ⟩

  interval 1 (1+ n) ∎

  where
    lemma₁ : 2× (𝟙^ n) + 2× (2^ n) ≡ 1+ (1+ (2× (2× (𝟙^ n))))
    lemma₁ = begin
      2× (𝟙^ n) + 2× (2^ n)

        ≡⟨ cong₂ _+_ refl (cong 2× (sym (1+𝟙^ n))) ⟩

      2× (𝟙^ n) + 2× (1+ (𝟙^ n))

        ≡⟨⟩

      2× (𝟙^ n) + 1+ (1+ (2× (𝟙^ n)))

        ≡⟨ +-suc _ _ ⟩

      1+ (2× (𝟙^ n) + 1+ (2× (𝟙^ n)))

        ≡⟨ cong 1+ (+-suc _ _) ⟩

      1+ (1+ (2× (𝟙^ n) + 2× (𝟙^ n)))

        ≡⟨ cong 1+ (cong 1+ (sym (2×-+ _))) ⟩

      1+ (1+ (2× (2× (𝟙^ n)))) ∎

    lemma₂ : (x : ℕ) → 1+ (1+ (2× (𝟙^ n) + x)) ≡ 2× (2^ n) * 1 + x
    lemma₂ x = begin
      1+ (1+ (2× (𝟙^ n) + x))

        ≡⟨⟩

      1+ (1+ (2× (𝟙^ n))) + x

        ≡⟨⟩

      2× (1+ (𝟙^ n)) + x

        ≡⟨ cong₂ _+_ (cong 2× (1+𝟙^ n)) refl ⟩

      2× (2^ n) + x

        ≡⟨ cong₂ _+_ (sym (*-identityʳ (2× (2^ n)))) refl ⟩

      2× (2^ n) * 1 + x ∎

------------------------------------------------------------

s : ℕ → List ℕ
s zero    = [ 0 ]
s (1+ n) = 0 ∷ (1⋯2^ (1+ n)) ⋎ s n

length-s : (n : ℕ) → length (s n) ≡ 𝟙^ (1+ n)
length-s zero = refl
length-s (1+ n) = begin
  length (s (1+ n))

    ≡⟨⟩

  length (0 ∷ (1⋯2^ (1+ n)) ⋎ s n)

    ≡⟨⟩

  1+ (length ((1⋯2^ (1+ n)) ⋎ s n))

    ≡⟨ cong 1+ (length-⋎ (1⋯2^ (1+ n)) (s n) (trans (length-1⋯2^ _) (sym (length-s n)))) ⟩

  1+ (length (1⋯2^ (1+ n)) + length (s n))

    ≡⟨ cong 1+ ( cong₂ _+_ (length-1⋯2^ (1+ n)) refl) ⟩

  1+ (𝟙^ (1+ n) + length (s n))

    ≡⟨ cong 1+ (cong₂ _+_ refl (length-s n)) ⟩

  1+ (𝟙^ (1+ n) + 𝟙^ (1+ n))

    ≡⟨ cong 1+ (sym (2×-+ _)) ⟩

  1+ (2× (𝟙^ (1+ n)))

    ≡⟨⟩

  𝟙^ (1+ (1+ n)) ∎

length-s≡1⋯2^ : (n : ℕ) → length (s n) ≡ length (1⋯2^ (1+ n))
length-s≡1⋯2^ n = trans (length-s n) (sym (length-1⋯2^ _))

s-prefix-∃ : (n : ℕ) → Σ[ ys ∈ List ℕ ] (s (1+ n) ≡ s n ++ ys)
s-prefix-∃ zero = 1 ∷ zero ∷ [] , refl
s-prefix-∃ (1+ n) with s-prefix-∃ n
... | (ys′ , eq) = ((2^ (1+ n) ⋯2^ (1+ (1+ n))) ⋎ ys′) ,
  (begin
    s (1+ (1+ n))

      ≡⟨⟩

    0 ∷ (1⋯2^ 1+ (1+ n)) ⋎ s (1+ n)

      ≡⟨ cong (_∷_ 0) (cong₂ _⋎_ (split-1⋯2^ (1+ n)) eq) ⟩

    0 ∷ ((1⋯2^ (1+ n)) ++ (2^ (1+ n) ⋯2^ (1+ (1+ n)))) ⋎ (s n ++ ys′)

      ≡⟨ cong (_∷_ 0) (sym (⋎-++₀ (1⋯2^ (1+ n)) _ _ _ (sym (length-s≡1⋯2^ n)))) ⟩

    0 ∷ ((1⋯2^ (1+ n)) ⋎ s n) ++ ((2^ (1+ n) ⋯2^ (1+ (1+ n))) ⋎ ys′)

      ≡⟨⟩

    s (1+ n) ++ ((2^ (1+ n) ⋯2^ (1+ (1+ n))) ⋎ ys′) ∎)

P : ℕ → List ℕ
P n = drop (𝟙^ n) (s n)

P-merge : (n : ℕ) → P (1+ n) ≡ (2^ n ⋯2^ (1+ n)) ⋎ P n
P-merge n = begin
  P (1+ n)

    ≡⟨⟩

  drop (𝟙^ (1+ n)) (s (1+ n))

    ≡⟨⟩

  drop (𝟙^ (1+ n)) (0 ∷ (1⋯2^ (1+ n)) ⋎ s n)

    ≡⟨⟩

  drop (2× (𝟙^ n)) ((1⋯2^ (1+ n)) ⋎ s n)

    ≡⟨ drop-⋎ (𝟙^ n) _ _ (sym (length-s≡1⋯2^ n)) ⟩

  drop (𝟙^ n) (1⋯2^ (1+ n)) ⋎ drop (𝟙^ n) (s n)

    ≡⟨⟩

  (2^ n ⋯2^ (1+ n)) ⋎ drop (𝟙^ n) (s n)

    ≡⟨⟩

  (2^ n ⋯2^ (1+ n)) ⋎ P n ∎


s-prefix : (n : ℕ) → s (1+ n) ≡ s n ++ P (1+ n)
s-prefix 0 = refl
s-prefix (1+ n) = begin
  s (1+ (1+ n))

    ≡⟨⟩

  0 ∷ (1⋯2^ 1+ (1+ n)) ⋎ s (1+ n)

    ≡⟨ cong (_∷_ 0) (cong₂ _⋎_ (split-1⋯2^ (1+ n)) (s-prefix n)) ⟩

  0 ∷ ((1⋯2^ (1+ n)) ++ (2^ (1+ n) ⋯2^ (1+ (1+ n)))) ⋎ (s n ++ P (1+ n))

    ≡⟨ cong (_∷_ 0) (sym (⋎-++₀ (1⋯2^ (1+ n)) _ _ _ (sym (length-s≡1⋯2^ n)))) ⟩

  0 ∷ ((1⋯2^ (1+ n)) ⋎ s n) ++ ((2^ (1+ n) ⋯2^ (1+ (1+ n))) ⋎ P (1+ n))

    ≡⟨⟩

  s (1+ n) ++ ((2^ (1+ n) ⋯2^ (1+ (1+ n))) ⋎ P (1+ n))

    ≡⟨ cong₂ _++_ refl (sym (P-merge (1+ n))) ⟩

  s (1+ n) ++ P (1+ (1+ n)) ∎

inorder-bt-merge : (n i : ℕ) → inorder (bt (1+ n) i) ≡ interval i n ⋎ inorder (bt n i)
inorder-bt-merge zero i rewrite +-identityʳ i | +-identityʳ i = refl
inorder-bt-merge (1+ n) i = begin
  inorder (bt (1+ (1+ n)) i)

    ≡⟨⟩

  inorder (Branch i (bt (1+ n) (2× i)) (bt (1+ n) (1+ (2× i))))

    ≡⟨⟩

  inorder (bt (1+ n) (2× i)) ++ [ i ] ++ inorder (bt (1+ n) (1+ (2× i)))

    ≡⟨ cong₂ _++_ (inorder-bt-merge n _) (cong (_++_ [ i ]) (inorder-bt-merge n _)) ⟩

  (interval (2× i) n ⋎ inorder (bt n (2× i)))
    ++ [ i ]
    ++ (interval (1+ (2× i)) n ⋎ inorder (bt n (1+ (2× i))))

    ≡⟨ sym (++-assoc _ [ i ] _) ⟩

  ((interval (2× i) n ⋎ inorder (bt n (2× i))) ++ [ i ])
    ++ (interval (1+ (2× i)) n ⋎ inorder (bt n (1+ (2× i))))

    ≡⟨ cong₂ _++_ {x = (interval (2× i) n ⋎ inorder (bt n (2× i))) ++ [ i ]}
         (⋎-snoc₁ _ _ _ (lemma₁ n _)) refl ⟩

  (interval (2× i) n ⋎ (inorder (bt n (2× i)) ++ [ i ]))
    ++ (interval (1+ (2× i)) n ⋎ inorder (bt n (1+ (2× i))))

    ≡⟨ ⋎-++₀ (interval (2× i) n) _ _ _ (lemma₂ n _ _) ⟩

  (interval (2× i) n ++ interval (1+ (2× i)) n)
    ⋎ ((inorder (bt n (2× i)) ++ [ i ]) ++ inorder (bt n (1+ (2× i))))

    ≡⟨ cong₂ _⋎_ (applyUpTo-++ (_+_ (2^ n * 2× i)) _ _ (2^ n) _ _ (lemma₃ n i) (lemma₄ n i) (sym (2×-+ _)))
                 (++-assoc _ [ i ] _)
     ⟩

  interval i (1+ n) ⋎ inorder (bt (1+ n) i)

  ∎
  where
    lemma₁ : (n i : ℕ) → length (interval i n) ≡ 1+ (length (inorder (bt n i)))
    lemma₁ n i = begin
      length (interval i n)

        ≡⟨ length-interval i n ⟩

      2^ n

        ≡⟨ sym (1+𝟙^ n) ⟩

      1+ (𝟙^ n)

        ≡⟨ cong 1+ (sym (trans (length-inorder (bt n i)) (btSize _))) ⟩

      1+ (length (inorder (bt n i))) ∎

    lemma₂ : (n i j : ℕ) → length (interval i n) ≡ length (inorder (bt n i) ++ [ j ])
    lemma₂ n i j = begin
      length (interval i n)

        ≡⟨ lemma₁ n _ ⟩

      1+ (length (inorder (bt n i)))

        ≡⟨ sym (+-comm _ 1) ⟩

      length (inorder (bt n i)) + 1

        ≡⟨ sym (length-++ (inorder (bt n i))) ⟩

      length (inorder (bt n i) ++ [ j ]) ∎

    lemma₃ : (n i k : ℕ) → k < 2^ n → 2^ n * 2× i + k ≡ 2× (2^ n) * i + k
    lemma₃ n _ k _ = cong₂ _+_ (*-2× (2^ n) _) refl

    lemma₄ : (n i k : ℕ) → k < 2^ n → 2^ n * 1+ (2× i) + k ≡ 2× (2^ n) * i + (2^ n + k)
    lemma₄ n i k _ rewrite (sym (+-assoc (2× (2^ n) * i) (2^ n) k)) =
      cong₂ _+_ (*-1+2× (2^ n) i) refl


P≡inorder-bt : (n : ℕ) → P n ≡ inorder (bt n 1) ++ [ 0 ]
P≡inorder-bt zero  = refl
P≡inorder-bt (1+ n) = begin
  P (1+ n)

    ≡⟨ P-merge n ⟩

  (2^ n ⋯2^ (1+ n)) ⋎ P n

    ≡⟨ cong₂ _⋎_ refl (P≡inorder-bt n) ⟩

  (2^ n ⋯2^ (1+ n)) ⋎ (inorder (bt n 1) ++ [ 0 ])

    ≡⟨ sym (⋎-snoc₁ _ _ _ lemma₁) ⟩

  ((2^ n ⋯2^ (1+ n)) ⋎ inorder (bt n 1)) ++ [ 0 ]

    ≡⟨ cong₂ _++_ (cong₂ _⋎_ (2⋯2^≡interval n) refl) refl ⟩

  (interval 1 n ⋎ inorder (bt n 1)) ++ [ 0 ]

    ≡⟨ cong₂ _++_ (sym (inorder-bt-merge n 1)) refl ⟩

  inorder (bt (1+ n) 1) ++ [ 0 ] ∎

  where
    lemma₁ : length (2^ n ⋯2^ (1+ n)) ≡ 1+ (length (inorder (bt n 1)))
    lemma₁ = begin
      length (2^ n ⋯2^ (1+ n))

        ≡⟨ length-2^⋯2^ n ⟩

      2^ n

        ≡⟨ sym (1+𝟙^ n) ⟩

      1+ (𝟙^ n)

        ≡⟨ cong 1+ (sym (btSize n)) ⟩

      1+ ∣ bt n 1 ∣

        ≡⟨ cong 1+ (sym (length-inorder (bt n 1))) ⟩

      1+ (length (inorder (bt n 1))) ∎

------------------------------------------------------------


record Monoid {ℓ} (A : Set ℓ) : Set ℓ where
  infixl 30 _⊕_
  field
    ε   : A
    _⊕_ : A → A → A
    -- inv : A → A

    .ε-identityˡ : (a : A) → ε ⊕ a ≡ a
    .ε-identityʳ : (a : A) → a ⊕ ε ≡ a
    .⊕-assoc     : (a b c : A) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    -- .invˡ        : (a : A) → inv a ⊕ a ≡ ε
    -- .invʳ        : (a : A) → a ⊕ inv a ≡ ε

open Monoid {{...}} public

instance
  NatMonoid : Monoid ℕ
  NatMonoid = record
    { ε           = 0
    ; _⊕_         = _+_
    ; ε-identityˡ = +-identityˡ
    ; ε-identityʳ = +-identityʳ
    ; ⊕-assoc     = +-assoc
    }
