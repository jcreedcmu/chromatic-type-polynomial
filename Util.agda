{-# OPTIONS --without-K --rewriting --cubical #-}
module Util where
open import Level public
open import Cubical.Foundations.Everything hiding (J ; ⟨_⟩ ; ⋆ ; Lift) public

_×_ : (A : Set) (B : Set) → Set
A × B = Σ A (λ _ → B)

data Maybe {i} (A : Set i) : Set i where
  Just : A → Maybe A
  None : Maybe A

data _⊞_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  Inl : A → A ⊞ B
  Inr : B → A ⊞ B

⊞e : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (A → C) → (B → C) → A ⊞ B → C
⊞e f g (Inl a) = f a
⊞e f g (Inr b) = g b
