{-# OPTIONS --without-K --rewriting --cubical  #-}

module chromatic.Circle where
open import Util
open import chromatic.Defns

data Nat : Set where
 z : Nat
 s : Nat → Nat

pred : Nat → Maybe Nat
pred z = None
pred (s x) = Just x

data Int : Set where
 Zero : Int
 Pos Neg : Nat → Int

succInt : Int → Int
succInt Zero = Pos z
succInt (Pos x) = Pos (s x)
succInt (Neg x) = liftm Neg Zero (pred x)

predInt : Int → Int
predInt Zero = Neg z
predInt (Neg x) = Neg (s x)
predInt (Pos x) = liftm Pos Zero (pred x)

succ-pred : section succInt predInt
succ-pred Zero = refl
succ-pred (Pos z) = refl
succ-pred (Pos (s x)) = refl
succ-pred (Neg z) = refl
succ-pred (Neg (s x)) = refl

pred-succ : section predInt succInt
pred-succ Zero = refl
pred-succ (Pos z) = refl
pred-succ (Pos (s x)) = refl
pred-succ (Neg z) = refl
pred-succ (Neg (s x)) = refl

data S1 : Set where
 base : S1
 loop : base ≡ base

sequiv : Int ≡ Int
sequiv = ua (isoToEquiv (iso succInt predInt succ-pred pred-succ))

Cover : S1 → Set
Cover base = Int
Cover (loop i) = sequiv i

encode : (x : S1) (p : base ≡ x) → Cover x
encode x p = subst Cover p Zero

natToLoop : Nat → base ≡ base
natToLoop z = loop
natToLoop (s x) = loop ∙ natToLoop x

intToLoop : Int → base ≡ base
intToLoop Zero = refl
intToLoop (Pos x) = natToLoop x
intToLoop (Neg x) = sym (natToLoop x)

S1-induction : (C : S1 → Set) (base' : C base) (loop' : base' ≡ subst C loop base')
   → (x : S1) → C x
S1-induction C base' loop' base = base'
S1-induction C base' loop' (loop i) = {!loop' i!}

data interval : Set where
 a b : interval
 path : a ≡ b

interval-induction : (C : interval → Set) (a' : C a) (b' : C b) (path' : PathP (λ i → C (path i)) a' b')
   → (x : interval) → C x
interval-induction C a' b' path' a = a'
interval-induction C a' b' path' b = b'
interval-induction C a' b' path' (path i) = path' i


check : (C : I → Set) (a : C i0) → transp (λ i → C (~ i)) i0 (transp C i0 a) ≡ a
check C aa j = transp (λ i → C ((~ i) ∧ (~ j))) j (transp (λ i → C (i ∧ (~ j))) j aa)








-- x : transp (λ j → C (path j)) i0 a'
interval-induction-helper : (C : interval → Set) (a' : C a) (b' : C b) →
   (subst C path a' ≡ b') → (PathP (λ i → C (path i)) a' b')
interval-induction-helper C a' b' x i = {! subst C (sym path) (subst C path a')!}

decode : (x : S1) (c : Cover x) → base ≡ x
decode base c = intToLoop c
decode (loop j) c i = {! !}
