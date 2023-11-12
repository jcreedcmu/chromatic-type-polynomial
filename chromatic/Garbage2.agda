{-# OPTIONS --without-K --rewriting --cubical  #-}

module chromatic.Garbage2 where
open import Util

module Foo where
  data Pth : Set where
    p0 p1 : Pth
    q : p0 ≡ p1

  data Sqr : Set where
    a b c d : Sqr
    ab : a ≡ b
    ac : a ≡ c
    bd : b ≡ d
    cd : c ≡ d
    abcd : ab ∙ bd ≡ ac ∙ cd

  path-ab : Pth → Sqr
  path-ab p0 = a
  path-ab p1 = b
  path-ab (q i) = ab i

  path-cd : Pth → Sqr
  path-cd p0 = c
  path-cd p1 = d
  path-cd (q i) = cd i

  thm : (p : Pth) → path-ab p ≡ path-cd p
  thm p0 = ac
  thm p1 = bd
  thm (q i) = {!!}

data S1 : Set where
   base : S1
   loop : base ≡ base

data G3 : Set where
   g : G3
   a b c : g ≡ g

abc : S1 → G3
abc base = g
abc (loop i) = (a ∙ b ∙ c) i

bca : S1 → G3
bca base = g
bca (loop i) = (b ∙ c ∙ a) i

-- not true
-- lemma : (a ∙ b ∙ c) ≡ (b ∙ c ∙ a)
-- lemma = {!!}

thm : (s : S1) → abc s ≡ bca s
thm base = a
thm (loop i) = {!!}

-- data ℕ : Set where
--  z : ℕ
--  s : ℕ → ℕ

-- data _<_ : ℕ → ℕ → Set where
--  <z : (n : ℕ) → z < s n
--  <s : (n m : ℕ) → n < m → (s n) < s m

-- postulate
--  ♯ : ℕ → Set

-- data 𝕌 (n : ℕ) : Set where
--  u v : 𝕌 n
--  p : ((m : ℕ) → m < n → ♯ m) → u ≡ v

-- record path {A : Set} (n : ℕ) (a b : A) : Set where
--  field
--   int : 𝕌 n → A
--   end1 : a ≡ int u
--   end2 : b ≡ int v

-- pathd : {A : Set} (n : ℕ) (a b : A) →  Set
-- pathd {A} n a b = ((m : ℕ) → m < n → ♯ m) → a ≡ b

-- thm : {A : Set} (n : ℕ) (a b c : A) → pathd n a b → pathd n b c → pathd n a c
-- thm n a b c p1 p2 sh = p1 sh ∙ p2 sh
