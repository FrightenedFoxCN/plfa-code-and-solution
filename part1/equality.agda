data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where
    infix 1 begin_
    infixr 2 _≡⟨⟩_ step-≡
    infix 3 _∎

    begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
    begin x≡y = x≡y

    _≡⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
    x ≡⟨⟩ x≡y = x≡y

    step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
    step-≡ x y≡z x≡y = trans x≡y y≡z

    syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

    _∎ : ∀ (x : A) → x ≡ x
    x ∎ = refl

open ≡-Reasoning

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

postulate
    +-identity : ∀ (m : ℕ) → m + zero ≡ m
    +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    begin
        m + zero
    ≡⟨ +-identity m ⟩
        m
    ≡⟨⟩
        zero + m
    ∎
+-comm m (suc n) =
    begin
        m + suc n
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩
        suc n + m
    ∎

data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ}
        → zero ≤ n
    
    s≤s : ∀ {m n : ℕ}
        → m ≤ n
        → suc m ≤ suc n

infix 4 _≤_

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n 
≤-refl {suc n} = s≤s ≤-refl

≤-refl′ : ∀ {n m : ℕ} → n ≡ m → n ≤ m
≤-refl′ refl = ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where
    infix 1 ≤-begin_
    infixr 2 _≤⟨⟩_ step-≤
    infix 3 _≤-∎

    ≤-begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
    ≤-begin x≤y = x≤y

    _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
    x ≤⟨⟩ x≤y = x≤y

    step-≤ : ∀ (x {y z} : ℕ) → y ≤ z → x ≤ y → x ≤ z
    step-≤ x y≤z x≤y = ≤-trans x≤y y≤z

    syntax step-≤ x y≤z x≤y = x ≤⟨ x≤y ⟩ y≤z

    _≤-∎ : ∀ (x : ℕ) → x ≤ x
    x ≤-∎ = ≤-refl

open ≤-Reasoning

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n zero m≤n = ≤-begin
        m + zero
    ≤⟨ ≤-refl′ (+-identity m) ⟩
        m
    ≤⟨ m≤n ⟩
        n
    ≤⟨ ≤-refl′ (sym (+-identity n)) ⟩
        n + zero
    ≤-∎
+-monoˡ-≤ m n (suc p) m≤n = ≤-begin
        m + suc p
    ≤⟨ ≤-refl′ (+-suc m p) ⟩
        suc (m + p)
    ≤⟨ s≤s (+-monoˡ-≤ m n p m≤n) ⟩
        suc (n + p)
    ≤⟨ ≤-refl′ (sym (+-suc n p)) ⟩
        n + suc p
    ≤-∎

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = ≤-begin
        suc n + p
    ≤⟨ ≤-refl′ (+-comm (suc n) p) ⟩
        p + suc n
    ≤⟨ ≤-refl′ (+-suc p n) ⟩
        suc (p + n)
    ≤⟨ ≤-refl′ (cong suc (+-comm p n)) ⟩
        suc (n + p)
    ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
        suc (n + q)
    ≤-∎

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-begin
        m + p
    ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
        n + p
    ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
        n + q
    ≤-∎

data even : ℕ → Set
data odd : ℕ → Set

data even where
    even-zero : even zero
    even-suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
    odd-suc : ∀ {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev rewrite +-comm n m = ev

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm′ m n = refl

{- rewriting can be written with `with` clause -}
even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n ev with m + n | +-comm m n
... | .(n + m) | refl = ev

even-comm′' : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′' m n = subst even (+-comm m n)

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = x≐y Q (refl-≐ P)
    where
        Q : A → Set
        Q z = P z → P x

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = x≐y Q refl
    where
        Q : A → Set
        Q z = x ≡ z

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
