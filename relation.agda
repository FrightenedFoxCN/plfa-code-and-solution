import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm; +-assoc; +-suc)
open import Data.Empty using (⊥; ⊥-elim)

{- indexed datatype here -}
data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} {- `z≤n` is a constructor name -}
        → zero ≤ n {- base case -}
    
    s≤s : ∀ {m n : ℕ}
        → m ≤ n
        → suc m ≤ suc n {- this two line is for inductive case -}

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

≤-refl : ∀ {n : ℕ}
    → n ≤ n

≤-refl {zero} = z≤n 
≤-refl {suc n} = s≤s ≤-refl

≤-suc : ∀ (n : ℕ) → n ≤ suc n
≤-suc zero = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
    → m ≤ p

≤-trans {zero} _ _ = z≤n 
≤-trans {suc m} {suc n} {suc p} (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

{- or written like this -}
≤-trans′ : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans′ z≤n _ = z≤n
≤-trans′ (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans′ m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

{- this is a datatype with parameters, looks like a disjunction -}
data Total (m n : ℕ) : Set where
    forward : m ≤ n → Total m n
    flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n 
≤-total (suc m) zero = flipped z≤n 
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)
{- the `with` clause is simply some implicit function -}

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q 
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n 
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n : ℕ} → zero < suc n
    s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

inv-s<s : ∀ {m n : ℕ} → suc m < suc n → m < n
inv-s<s (s<s m<n) = m<n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s 
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy (m n : ℕ) : Set where
    <-forward : m < n → Trichotomy m n
    <-flipped : n < m → Trichotomy m n
    <-equal : m ≡ n → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = <-equal refl
<-trichotomy zero (suc n) = <-forward z<s
<-trichotomy (suc m) zero = <-flipped z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n 
... | <-forward m<n = <-forward (s<s m<n)
... | <-flipped n<m = <-flipped (s<s n<m)
... | <-equal m≡n = <-equal (cong suc m≡n)

+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤→< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤→< {zero} {suc n} m≤n = z<s 
≤→< {suc m} {suc n} m≤n = s<s (≤→< (inv-s≤s m≤n))

<→≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<→≤ {zero} {suc n} m<n = s≤s z≤n
<→≤ {suc m} {suc n} m<n = s≤s (<→≤ (inv-s<s m<n))

<-trans-revisited : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n p m<n n<p = ≤→< (≤-trans (≤-trans (<→≤ m<n) (≤-suc n)) (<→≤ n<p))

data even : ℕ → Set
data odd : ℕ → Set

data even where
    zero : even zero
    suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
    suc : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc x) en = suc (o+e≡o x en) 
o+e≡o (suc x) en = suc (e+e≡e x en)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e {suc m} {n} (suc em) on rewrite +-comm m n = suc (o+e≡o on em)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0 
from (n O) = 2 * (from n)
from (n I) = 2 * (from n) + 1

data One : Bin → Set where
    one : One (⟨⟩ I)
    append-O : ∀ {b : Bin} → One b → One (b O)
    append-I : ∀ {b : Bin} → One b → One (b I)

data Can : Bin → Set where
    zero : Can (⟨⟩ O)
    other : ∀ {b : Bin} → One b → Can b

inc-One : ∀ {b : Bin} → One b → One (inc b)
inc-One one = append-O one
inc-One (append-O ob) = append-I ob
inc-One (append-I ob) = append-O (inc-One ob)

inc-Can : ∀ {b : Bin} → Can b → Can (inc b)
inc-Can zero = other one
inc-Can (other ob) = other (inc-One ob)

to-Can : ∀ (n : ℕ) → Can (to n)
to-Can zero = zero 
to-Can (suc n) = inc-Can (to-Can n)

One→1≤fb : ∀ {b : Bin} → One b → 1 ≤ from b
One→1≤fb one = ≤-refl
One→1≤fb {b O} (append-O ob) rewrite *-comm 2 (from b) = *-mono-≤ 1 (from b) 1 2 (One→1≤fb ob) (s≤s z≤n)
One→1≤fb {b I} (append-I ob) rewrite +-identityʳ (from b) | +-comm (from b + from b) 1 = s≤s z≤n

1≤fb→to-double : ∀ {n : ℕ} → 1 ≤ n → to (n * 2) ≡ (to n) O
1≤fb→to-double {suc zero} 1≤n = refl
1≤fb→to-double {suc (suc n)} 1≤n rewrite 1≤fb→to-double {suc n} (s≤s z≤n)  = refl

One-to-from-adj : ∀ {b : Bin} → One b → to (from b) ≡ b
One-to-from-adj one = refl
One-to-from-adj {b O} (append-O ob) rewrite *-comm 2 (from b) | 1≤fb→to-double (One→1≤fb ob) | One-to-from-adj ob = refl
One-to-from-adj {b I} (append-I ob) rewrite +-comm (2 * from b) 1 | *-comm 2 (from b) | cong inc (1≤fb→to-double (One→1≤fb ob)) | One-to-from-adj ob = refl

Can-to-from-adj : ∀ {b : Bin} → Can b → to (from b) ≡ b
Can-to-from-adj zero = refl             
Can-to-from-adj (other x) = One-to-from-adj x  