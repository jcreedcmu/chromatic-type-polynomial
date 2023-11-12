{-# OPTIONS --without-K --rewriting --cubical #-}

module chromatic.Garbage where
open import Util

-- hfib : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (f : A → B) (b : B) → Set (ℓA ⊔ ℓB)
-- hfib {A = A} f b = Σ A (λ a → f a ≡ b)

data ⊤ {ℓ : Level} : Set ℓ where
  * : ⊤

data ℕ : Set where
   zz : ℕ
   ss : ℕ → ℕ


-- postulate
--   pushout : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
--             (fA : C → A) (fb : C → B) → Set (ℓA ⊔ ℓB ⊔ ℓC)

-- data Bound : ℕ → Set
-- data Flat : {n : ℕ} (b : Bound n) → Set
-- RealizeBound : {n : ℕ} (b : Bound n) → Set
-- RealizeFlat : {n : ℕ} (b : Bound n) (ϕ : Flat b) → Set
-- Comp : {n : ℕ} (b1 b2 b3 : Bound n) → Set

-- data Bound where
--   bound/0 : Bound zz
--   bound/s : {n : ℕ} (b : Bound n) (dom : Flat b) (cod : Flat b) → Bound (ss n)

-- data Flat where
--   flat/fill : {n : ℕ} (b : Bound n) → Flat b
--   flat/comp : {n : ℕ} (b1 b2 b3 : Bound n) (ϕ1 : Flat b1) (ϕ2 : Flat b2) (k : Comp b1 b2 b3) → Flat b3
--   flat/id : {n : ℕ} (b : Bound n) (ϕ : Flat b) → Flat {ss n} (bound/s b ϕ ϕ)


-- RealizeBound = {!!}
-- RealizeFlat = {!!}
-- Comp = {!!}
