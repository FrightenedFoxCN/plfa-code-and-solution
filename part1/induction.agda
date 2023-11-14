import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = 
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎ 
+-assoc (suc m) n p = begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩ {- a justification of the proof, meaning that suc is a congruence -}
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

{- following rewrite system is employed to simplify the proof -}
+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl 
{- rewriting by a given equation is indicated by the keyword `rewrite` followed by a proof of that equation -}
+-identity (suc n) rewrite (+-identity n) = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl 
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl 
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

{- several exercises here -}
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
{- `sym` swaps the two side of the equality -}
+-swap m n p rewrite sym (+-assoc m n p) | sym (+-assoc n m p) | +-comm m n  = refl

*-zero : ∀ (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) rewrite *-zero n = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero rewrite *-zero (m + n) | *-zero m | *-zero n = refl  
*-distrib-+ zero n (suc p) rewrite +-identity n = refl 
*-distrib-+ (suc m) n (suc p) rewrite *-distrib-+ m n (suc p) | +-assoc p (m * suc p) (n * suc p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl 
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-identity : ∀ (n : ℕ) → n * 1 ≡ n
*-identity zero = refl
*-identity (suc n) rewrite *-identity n = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zero m = refl
*-comm zero (suc n) rewrite *-zero (suc n) = refl 
*-comm (suc m) (suc n) rewrite *-comm m n | *-comm m (suc n) | sym (+-assoc n m (n * m)) | +-comm n m | +-assoc m n (n * m) | *-comm n (suc m) | *-comm m n = refl

∸-zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-zero zero = refl 
∸-zero (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite ∸-zero n | ∸-zero p | ∸-zero (n + p) = refl 
∸-+-assoc (suc m) zero p = refl 
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identity (m ^ p) = refl 
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p) = refl 

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl 
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p | sym (*-assoc (m * n) (m ^ p) (n ^ p)) | *-assoc m n (m ^ p) | *-comm n (m ^ p) | sym (*-assoc m (m ^ p) n) | *-assoc (m * (m ^ p)) n (n ^ p) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zero n = refl 
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p rewrite sym (^-distribˡ-+-* m n (n * p)) | *-comm n (suc p) | *-comm n p = refl

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

inc-adj-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-adj-suc ⟨⟩ = refl 
inc-adj-suc (b O) rewrite +-comm (from b + (from b + 0)) 1  = refl
inc-adj-suc (b I) rewrite inc-adj-suc b | +-identity (suc (from b)) | +-identity (from b) | +-assoc (from b) (from b) 1 | +-comm (from b) 1 = refl

{- The second equality seems to hold, but it doesn't due to 
multiple possible representation of a same natural number -}

from-to-inv : ∀ (n : ℕ) → from (to n) ≡ n
from-to-inv zero = refl 
from-to-inv (suc n) rewrite inc-adj-suc (to n) | from-to-inv n = refl