data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

{- first exercise: seven -}
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

{- this is the definition of plus -}
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

{- we shall prove the fact -}

_ : 2 + 3 ≡ 5
_ =
    begin
        2 + 3
    ≡⟨⟩
        (suc (suc zero) + (suc (suc (suc zero))))
    ≡⟨⟩
        suc ((suc zero) + (suc (suc (suc zero))))
    ≡⟨⟩
        suc (suc (zero + suc (suc (suc zero))))
    ≡⟨⟩
        suc (suc (suc (suc (suc zero))))
    ≡⟨⟩
        5
    ∎

{- second exercise: +-example -}
_ : 3 + 4 ≡ 7
_ = refl

{- then define multiplication -}
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

{- third exercise: *-example -}
_ = 3 * 4
_ =
    begin
        3 * 4
    ≡⟨⟩
        4 + (2 * 4)
    ≡⟨⟩ {- note that the brace should not be omitted! -}
        4 + (4 + (1 * 4))
    ≡⟨⟩
        4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩
        4 + (4 + (4 + 0))
    ≡⟨⟩
        12
    ∎

{- fourth exercise: _^_ -}
_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
    begin
        3 ^ 4
    ≡⟨⟩
        3 * (3 ^ 3)
    ≡⟨⟩
        3 * (3 * (3 ^ 2))
    ≡⟨⟩
        3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
        3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
        3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩
        81
    ∎

{- then define monus -}
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ n = zero
(suc m) ∸ (suc n) = m ∸ n

{- the fifth exercise: ∸-example -}
_ : 5 ∸ 3 ≡ 2
_ =
    begin
        5 ∸ 3
    ≡⟨⟩
        4 ∸ 2
    ≡⟨⟩
        3 ∸ 1
    ≡⟨⟩
        2 ∸ 0
    ≡⟨⟩
        2
    ∎

_ : 3 ∸ 5 ≡ 0
_ = refl

{- precedence can be set like following -}
infixl 6 _+_ _∸_
infixl 7 _*_

{- using more pragmas -}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

{- the sixth exercise: binary -}
data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

{- testing that it's true by four -}
_ : inc (inc (inc (inc ⟨⟩))) ≡ (⟨⟩ I O O)
_ =
    begin
        inc (inc (inc (inc ⟨⟩)))
    ≡⟨⟩
        inc (inc (inc (⟨⟩ I)))
    ≡⟨⟩
        inc (inc ((inc ⟨⟩) O))
    ≡⟨⟩
        inc (inc (⟨⟩ I O))
    ≡⟨⟩
        inc (⟨⟩ I I)
    ≡⟨⟩
        (inc (⟨⟩ I)) O
    ≡⟨⟩
        ((inc ⟨⟩) O) O
    ≡⟨⟩
        ⟨⟩ I O O
    ∎

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

{- testing the function by eleven -}
_ : to 11 ≡ (⟨⟩ I O I I)
_ = refl

from : Bin → ℕ
from ⟨⟩ = 0 
from (n O) = 2 * (from n)
from (n I) = 2 * (from n) + 1

{- testing the function by eleven -}
_ : from (⟨⟩ I O I I) ≡ 11
_ = refl