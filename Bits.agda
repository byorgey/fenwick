open import Data.Bool using (true ; false)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Bit : Set where
  O : Bit
  I : Bit

_≟B_ : Decidable {A = Bit} _≡_
O ≟B O = yes refl
O ≟B I = no (λ ())
I ≟B O = no (λ ())
I ≟B I = yes refl

data Bits : Set where
  Rep : Bit → Bits
  _∷_ : Bits → Bit → Bits

infixl 30 _∷_

variable
  b x y : Bit
  bs : Bits

expand : Bits → Bits
expand (Rep b) = Rep b ∷ b
expand (bs ∷ b) = bs ∷ b

_∷′_ : Bits → Bit → Bits
Rep b ∷′ b′ with b ≟B b′
... | no _ = Rep b ∷ b′
... | yes _ = Rep b
(bs ∷ b) ∷′ b′ = (bs ∷ b) ∷ b′

Normalized : Bits → Set
Normalized (Rep b) = ⊤
Normalized (Rep b ∷ b′) = b ≢ b′
Normalized ((bs ∷ b) ∷ _) = Normalized (bs ∷ b)

∷′-Normalized : Normalized bs → Normalized (bs ∷′ b)
∷′-Normalized {Rep b} {b′} _ with b ≟B b′
... | no ¬a = ¬a
... | yes a = tt
∷′-Normalized {Rep b ∷ b′} b≢b′ = b≢b′
∷′-Normalized {bs ∷ b ∷ _} norm = norm

normalize : Bits → Σ Bits Normalized
normalize (Rep b) = Rep b , tt
normalize (Rep b ∷ b′) with b ≟B b′
... | no ¬a = Rep b ∷ b′ , ¬a
... | yes a = Rep b , tt
normalize ((bs ∷ b) ∷ b′) with normalize (bs ∷ b)
... | bs′ ∷ x , norm = bs′ ∷ x ∷ b′ , norm
... | Rep x , norm with x ≟B b′
... | no ¬a = Rep x ∷ b′ , ¬a
... | yes a = Rep x , tt

infix 10 _≅_

_≅_ : Bits → Bits → Set
Rep x ≅ Rep y = x ≡ y
Rep x ≅ ys ∷ y = (x ≡ y) × (Rep x ≅ ys)
xs ∷ x ≅ Rep y = (x ≡ y) × (xs ≅ Rep y)
xs ∷ x ≅ ys ∷ y = (x ≡ y) × (xs ≅ ys)

≅-refl : bs ≅ bs
≅-refl {Rep x} = refl
≅-refl {bs ∷ x} = refl , ≅-refl

≅-sym : {xs ys : Bits} → xs ≅ ys → ys ≅ xs
≅-sym {Rep O} {Rep O} xs≅ys = refl
≅-sym {Rep O} {ys ∷ O} xs≅ys = refl , ≅-sym (proj₂ xs≅ys)
≅-sym {Rep I} {Rep I} xs≅ys = refl
≅-sym {Rep I} {ys ∷ I} xs≅ys = refl , ≅-sym (proj₂ xs≅ys)
≅-sym {xs ∷ O} {Rep O} xs≅ys = refl , ≅-sym (proj₂ xs≅ys)
≅-sym {xs ∷ O} {ys ∷ O} xs≅ys = refl , ≅-sym (proj₂ xs≅ys)
≅-sym {xs ∷ I} {Rep I} xs≅ys = refl , ≅-sym (proj₂ xs≅ys)
≅-sym {xs ∷ I} {ys ∷ I} xs≅ys = refl , ≅-sym (proj₂ xs≅ys)

≅-trans : {xs ys zs : Bits} → xs ≅ ys → ys ≅ zs → xs ≅ zs
≅-trans {Rep O} {Rep O} {Rep O} e1 e2 = refl
≅-trans {Rep O} {Rep O} {zs ∷ x} e1 e2 = e2
≅-trans {Rep O} {ys ∷ O} {Rep O} e1 e2 = refl
≅-trans {Rep O} {ys ∷ O} {zs ∷ O} (_ , e1) (_ , e2) = refl , ≅-trans e1 e2
≅-trans {Rep I} {Rep I} {Rep I} e1 e2 = refl
≅-trans {Rep I} {Rep I} {zs ∷ I} e1 e2 = refl , proj₂ e2
≅-trans {Rep I} {ys ∷ I} {Rep I} e1 e2 = refl
≅-trans {Rep I} {ys ∷ I} {zs ∷ I} e1 e2 = refl , ≅-trans (proj₂ e1) (proj₂ e2)
≅-trans {xs ∷ O} {Rep O} {Rep O} e1 e2 = refl , proj₂ e1
≅-trans {xs ∷ O} {Rep O} {zs ∷ O} e1 e2 = refl , ≅-trans (proj₂ e1) (proj₂ e2)
≅-trans {xs ∷ I} {Rep I} {Rep I} e1 e2 = refl , proj₂ e1
≅-trans {xs ∷ I} {Rep I} {zs ∷ I} e1 e2 = refl , ≅-trans (proj₂ e1) (proj₂ e2)
≅-trans {xs ∷ O} {ys ∷ O} {Rep O} e1 e2 = refl , ≅-trans (proj₂ e1) (proj₂ e2)
≅-trans {xs ∷ O} {ys ∷ O} {zs ∷ O} e1 e2 = refl , ≅-trans (proj₂ e1) (proj₂ e2)
≅-trans {xs ∷ I} {ys ∷ I} {Rep I} e1 e2 = refl , ≅-trans (proj₂ e1) (proj₂ e2)
≅-trans {xs ∷ I} {ys ∷ I} {zs ∷ I} e1 e2 = refl , ≅-trans (proj₂ e1) (proj₂ e2)

normalize-≅ : bs ≅ proj₁ (normalize bs)
normalize-≅ {Rep x} = refl
normalize-≅ {Rep b ∷ b′} with b ≟B b′
... | no _ = refl , refl
... | yes a = sym a , refl
normalize-≅ {bs ∷ b ∷ b′} with normalize (bs ∷ b)
... | bs′ ∷ x , norm = refl , {!!} , {!!}
... | Rep x , norm = {!!}

------------------------------------------------------------

invBit : Bit → Bit
invBit O = I
invBit I = O

inv : Bits → Bits
inv (Rep x) = Rep (invBit x)
inv (bs ∷ x) = inv bs ∷ invBit x

_∧_ : Bit → Bit → Bit
O ∧ _ = O
I ∧ b = b

∧-invBit : {x : Bit} → x ∧ invBit x ≡ O
∧-invBit {O} = refl
∧-invBit {I} = refl

_∨_ : Bit → Bit → Bit
I ∨ _ = I
O ∨ b = b

_&_ : Bits → Bits → Bits
Rep x & Rep y = Rep (x ∧ y)
Rep x & (ys ∷ y) = (Rep x & ys) ∷ (x ∧ y)
(xs ∷ x) & Rep y = (xs & Rep y) ∷ (x ∧ y)
(xs ∷ x) & (ys ∷ y) = (xs & ys) ∷ (x ∧ y)

&-inv : bs & inv bs ≅ Rep O
&-inv {Rep x} = ∧-invBit {x}
&-inv {bs ∷ x} = ∧-invBit {x} , &-inv

inc : Bits → Bits
inc (Rep I) = Rep O
inc (Rep O) = Rep O ∷ I
inc (bs ∷ O) = bs ∷ I
inc (bs ∷ I) = inc bs ∷ O

inc-≅ : {xs ys : Bits} → xs ≅ ys → inc xs ≅ inc ys
inc-≅ {Rep O} {Rep O} eq = refl , refl
inc-≅ {Rep I} {Rep I} eq = refl
inc-≅ {Rep O} {ys ∷ O} (_ , eq) = refl , eq
inc-≅ {Rep I} {ys ∷ I} (_ , eq) = refl , (inc-≅ eq)
inc-≅ {xs ∷ O} {Rep O} eq = refl , proj₂ eq
inc-≅ {xs ∷ O} {ys ∷ O} eq = refl , proj₂ eq
inc-≅ {xs ∷ I} {Rep I} eq = refl , inc-≅ (proj₂ eq)
inc-≅ {xs ∷ I} {ys ∷ I} eq = refl , inc-≅ (proj₂ eq)

dec : Bits → Bits
dec (Rep O) = Rep I
dec (Rep I) = Rep I ∷ O
dec (bs ∷ I) = bs ∷ O
dec (bs ∷ O) = dec bs ∷ I

inc-dec : inc (dec bs) ≅ bs
inc-dec {Rep O} = refl
inc-dec {Rep I} = refl , refl
inc-dec {bs ∷ O} = refl , inc-dec
inc-dec {bs ∷ I} = refl , ≅-refl

dec-inc : dec (inc bs) ≅ bs
dec-inc {Rep O} = refl , refl
dec-inc {Rep I} = refl
dec-inc {bs ∷ O} = refl , ≅-refl
dec-inc {bs ∷ I} = refl , dec-inc

lsb : Bits → Bits
lsb (Rep O) = Rep O
lsb (Rep I) = Rep O ∷ I
lsb (bs ∷ I) = Rep O ∷ I
lsb (bs ∷ O) = lsb bs ∷ O

_+_ : Bits → Bits → Bits
Rep O + ys = ys
Rep I + Rep O = Rep I
Rep I + Rep I = Rep I ∷ O
Rep I + (ys ∷ O) = (Rep I + ys) ∷ I
Rep I + (ys ∷ I) = inc (Rep I + ys) ∷ O
(xs ∷ x) + Rep O = xs ∷ x
(xs ∷ O) + Rep I = (xs + Rep I) ∷ I
(xs ∷ I) + Rep I = inc (xs + Rep I) ∷ O
(xs ∷ O) + (ys ∷ y) = (xs + ys) ∷ y
(xs ∷ I) + (ys ∷ O) = (xs + ys) ∷ I
(xs ∷ I) + (ys ∷ I) = inc (xs + ys) ∷ O

neg : Bits → Bits
neg bs = inc (inv bs)

+0 : bs + Rep O ≅ bs
+0 {Rep O} = refl
+0 {Rep I} = refl
+0 {bs ∷ x} = refl , ≅-refl

+-inc : {xs ys : Bits} → xs + inc ys ≅ inc (xs + ys)
+-inc {Rep O} {Rep O} = refl , refl
+-inc {Rep I} {Rep O} = refl , refl
+-inc {xs ∷ O} {Rep O} = refl , +0
+-inc {xs ∷ I} {Rep O} = refl , (inc-≅ +0)
+-inc {Rep O} {Rep I} = refl
+-inc {Rep I} {Rep I} = refl , refl
+-inc {xs ∷ O} {Rep I} = refl , ≅-trans (≅-sym +0) (+-inc {xs} {Rep I})
+-inc {xs ∷ I} {Rep I} = refl , ≅-trans (≅-sym +0) (+-inc {xs} {Rep I})
+-inc {Rep O} {ys ∷ x} = ≅-refl
+-inc {Rep I} {ys ∷ O} = refl , ≅-refl
+-inc {Rep I} {ys ∷ I} = refl , +-inc {Rep I} {ys}
+-inc {xs ∷ O} {ys ∷ O} = refl , ≅-refl
+-inc {xs ∷ O} {ys ∷ I} = refl , +-inc {xs} {ys}
+-inc {xs ∷ I} {ys ∷ O} = refl , ≅-refl
+-inc {xs ∷ I} {ys ∷ I} = refl , +-inc {xs} {ys}

+-neg : bs + neg bs ≅ Rep O
+-neg {Rep O} = refl
+-neg {Rep I} = refl , refl
+-neg {bs ∷ O} = refl , +-neg {bs}
+-neg {bs ∷ I} = refl , ≅-trans (≅-sym (+-inc {bs} {inv bs})) (+-neg {bs})

lsb-neg : lsb bs ≅ (bs & neg bs)
lsb-neg {Rep O} = refl
lsb-neg {Rep I} = refl , refl
lsb-neg {bs ∷ O} = refl , lsb-neg
lsb-neg {bs ∷ I} = refl , (≅-sym &-inv)

------------------------------------------------------------

atLSB : (Bits → Bits) → Bits → Bits
atLSB _ (Rep O) = Rep O
atLSB f (Rep I) = f (Rep I)
atLSB f (bs ∷ O) = atLSB f bs ∷ O
atLSB f (bs ∷ I) = f (bs ∷ I)

+lsb : bs + lsb bs ≅ atLSB inc bs
+lsb {Rep O} = refl
+lsb {Rep I} = refl , refl
+lsb {bs ∷ O} = refl , +lsb {bs}
+lsb {bs ∷ I} = refl , (inc-≅ +0)
