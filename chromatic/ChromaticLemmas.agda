{-# OPTIONS --without-K --rewriting --cubical  #-}

module chromatic.ChromaticLemmas where
open import Util
open import chromatic.Defns

-- constantly refl function
crefl : {X : Set} (x : X) → x ≡ x
crefl = λ x → refl {x = x}

module FromGraph (G : Graph) (∂ : GBd G) where
  open Graph G
  G0 : (Maybe E → J) → Graph
  G0 S = (graph/ V (⋆ S) (liftm b ∂ ∘ 𝕖 S))

  module _ (j : J) (S : E → J) where
   E1 : Set
   E1 = (⋆ (liftm S j))

   G1 : Graph
   G1 = (graph/ V E1 (liftm b ∂ ∘ 𝕖 (liftm S j)))

   E2 : Set
   E2 = (⋆ S ⊞ jbar j)

   G2 : Graph
   G2 = (graph/ V E2 (⊞e (b ∘ 𝕖 S) (λ _ → ∂)))

   G3 : Graph
   G3 = (graph/ (contractTypeBy V ∂ (jbar j)) (⋆ S) (square inject ∘ b ∘ 𝕖 S))

maybe-lemma0 : {A B : Set} → ((Maybe A) → B) ≡ B × (A → B)
maybe-lemma0 = ua (isoToEquiv (iso fore back (λ b i → b) back-fore)) where
 fore : {A B : Set} → ((Maybe A) → B) → B × (A → B)
 fore f =  (f None) , (f ∘ Just)

 back : {A B : Set} → B × (A → B) → ((Maybe A) → B)
 back (b , f) m = liftm f b m

 back-fore : {A B : Set} (f : Maybe A → B) → back (fore f) ≡ f
 back-fore f i (Just x) = f (Just x)
 back-fore f i None = f None

sigma-prod-split : {A B : Set} {C : (A × B) → Set} →
  Σ (A × B) C ≡ Σ A \ b → Σ B \ f → C (b , f)
sigma-prod-split {A} {B} {C} = ua (isoToEquiv (iso fore back crefl crefl)) where
 T1 = Σ (A × B) C
 T2 = Σ A \ a → Σ B \ b → C (a , b)

 fore : T1 → T2
 fore ((a , b) , c) = a , (b , c)

 back : T2 → T1
 back (a , (b , c)) = (a , b) , c

Σ-cong-fst : {A A' : Set} {B : A' → Set} (p : A ≡ A') → Σ A (B ∘ transport p) ≡ Σ A' B
Σ-cong-fst {B = B} p i = Σ (p i) (B ∘ transp (λ j → p (i ∨ j)) i)

-- refl transport. I feel like I shouldn't need to faff around like
-- this. maybe there's some better way of defining Σ-cong-fst or
-- maybe-lemma0 that doesn't produce trans at i0?
rt : {A : Set} (a : A) → A
rt a = transport refl a

rt=id : {A : Set} (a : A) → rt a ≡ a
rt=id {A} a i = transp (λ i → A) i a

maybe-lemma : {A B : Set} {C : (Maybe A → B) → Set} →
  Σ (Maybe A → B) C ≡ Σ B \ b → Σ (A → B) \ f → C (liftm f b)
maybe-lemma {A} {B} {C} =
  (Σ (Maybe A → B) C)
    ≡⟨ sym (Σ-cong-fst (sym (maybe-lemma0))) ⟩
  (Σ (B × (A → B)) (C ∘ λ a m → liftm (rt (snd a)) (rt (fst a)) m))
    ≡⟨ (λ i → (Σ (B × (A → B)) (C ∘ λ a m → liftm (rt=id (snd a) i) (rt=id (fst a) i) m))) ⟩
  (Σ (B × (A → B)) (C ∘ λ a m → liftm (snd a) (fst a) m))
    ≡⟨ sigma-prod-split ⟩
  (Σ B \ b → Σ (A → B) \ f → C (liftm f b))
  ∎

-- Somehow this seems suboptimal that I have to bother doing this
transport-thm : {A B : Set} (im : Iso A B) → transport (λ i → ua (isoToEquiv im) (~ i)) ≡ Iso.inv im
transport-thm im i a = Iso.inv im (rt=id a i)

module E1≈E2 {E : Set} (j : J) (S : E → J) where
 fore : ⋆ (liftm S j) → ⋆ S ⊞ jbar j
 fore ((Just e , q) , p) = Inl ((e , q) , p)
 fore ((None , q) , p) = Inr (q , p)

 back : ⋆ S ⊞ jbar j → ⋆ (liftm S j)
 back (Inl ((e , q) , p)) = ((Just e , q) , p)
 back (Inr (q , p)) = ((None , q) , p)

 fore-back : section fore back
 fore-back x@(Inl _) i = x
 fore-back x@(Inr _) i = x

 back-fore : section back fore
 back-fore x@((Just _ , _) , _) i = x
 back-fore x@((None , _) , _) i = x

 im : Iso (⋆ (liftm S j)) (⋆ S ⊞ jbar j)
 im = iso fore back fore-back back-fore

E1=E2 : {E : Set} (j : J) (S : E → J) → ⋆ (liftm S j) ≡ ⋆ S ⊞ jbar j
E1=E2 j S = ua (isoToEquiv (E1≈E2.im j S))

boundary-lemma0a : {E W : Set} {∂ : W} (b : E → W) (j : J) (S : E → J) →
    ((liftm b ∂ ∘ 𝕖 (liftm S j)) ∘ E1≈E2.back j S)
  ≡ (⊞e (b ∘ 𝕖 S) (λ _ → ∂))
boundary-lemma0a b j S i (Inl ((e , _) , _)) = b e
boundary-lemma0a {∂ = ∂} b j S i (Inr _) = ∂

boundary-lemma0 : {E W : Set} {∂ : W} (b : E → W) (j : J) (S : E → J)
  → ((liftm b ∂ ∘ 𝕖 (liftm S j)) ∘ transport (λ i → E1=E2 j S (~ i)))
     ≡ (⊞e (b ∘ 𝕖 S) (λ _ → ∂))
boundary-lemma0 {E} {W} {∂} b j S =
    ((liftm b ∂ ∘ 𝕖 (liftm S j)) ∘ transport (λ i → E1=E2 j S (~ i)))
    ≡⟨ (λ i → (liftm b ∂ ∘ 𝕖 (liftm S j)) ∘ (transport-thm (E1≈E2.im j S) i)) ⟩
    ((liftm b ∂ ∘ 𝕖 (liftm S j)) ∘ E1≈E2.back j S)
    ≡⟨ boundary-lemma0a b j S ⟩
    (⊞e (b ∘ 𝕖 S) (λ _ → ∂))
    ∎

RG2=RG3-lemma : {V jb : Set} {∂ : Bd V} (S : Set) (f : S → V × V) →
  Realize (graph/ V (S ⊞ jb) (⊞e f (λ _ → ∂))) ≡
  Realize (graph/ (contractTypeBy V ∂ jb) S (square inject ∘ f))
RG2=RG3-lemma {V}{jb} {∂} S f = ua (isoToEquiv (iso fore back fore-back back-fore)) where
   T1 = Realize (graph/ V (S ⊞ jb) (⊞e f (λ _ → ∂)))
   T2 = Realize (graph/ (contractTypeBy V ∂ jb) S (square inject ∘ f))
   fore : T1 → T2
   fore (ri v) = ri (inject v)
   fore (rp (Inl s) i) = rp s i
   fore (rp (Inr ϕ) i) = ri (theyre-equal ϕ i)

   back : T2 → T1
   back (ri (inject v)) = ri v
   back (ri (theyre-equal ϕ i)) = rp (Inr ϕ) i
   back (rp s i) = rp (Inl s) i

   fore-back : section fore back
   fore-back (ri (inject v)) = refl
   fore-back (ri (theyre-equal ϕ i)) = refl
   fore-back (rp s i) = refl

   back-fore : section back fore
   back-fore (ri v) = refl
   back-fore (rp (Inl s) i) = refl
   back-fore (rp (Inr ϕ) i) = refl

module _ where
 open Graph

 graph-edge-cong : {E' : Set} (G : Graph) (p : E' ≡ G .E) →
    G ≡ graph/ (G .V) E' (G .b ∘ transport p)
 graph-edge-cong G@(graph/ V E b) p i = graph/ V (p (~ i)) (λ x → b (transp (λ j → p (~ i ∨ j)) (~ i) x))

 boundary-lemma : {G : Graph} {∂ : GBd G} (j : J) (S : G .E → J)
   → ((liftm (G .b) ∂ ∘ 𝕖 (liftm S j)) ∘ transport (λ i → E1=E2 j S (~ i)))
      ≡ (⊞e ((G .b) ∘ 𝕖 S) (λ _ → ∂))
 boundary-lemma {G} {∂} j S = boundary-lemma0 {G .E} {G .V × G .V} {∂} (G .b) j S

 G1=G2 : {G : Graph} {∂ : GBd G} (j : J) (S : G .E → J) →
   (graph/ (G .V) (⋆ (liftm S j)) (liftm (G .b) ∂ ∘ 𝕖 (liftm S j))) ≡
   (graph/ (G .V) (⋆ S ⊞ jbar j) (⊞e ((G .b) ∘ 𝕖 S) (λ _ → ∂)))
 G1=G2 {G} {∂} j S =
    (FromGraph.G1 G ∂ j S)
      ≡⟨ graph-edge-cong (FromGraph.G1 G ∂ j S) (sym (E1=E2 j S)) ⟩
    (graph/ (G .V) (⋆ S ⊞ jbar j)
      ((liftm (G .b) ∂ ∘ 𝕖 (liftm S j)) ∘ transport (λ i → E1=E2 j S (~ i))))
      ≡⟨ (λ i → graph/ (G .V) (⋆ S ⊞ jbar j) ((boundary-lemma {G} {∂} j S i))) ⟩
    (FromGraph.G2 G ∂ j S)
      ∎

 RG2=RG3 : {G : Graph} {∂ : GBd G} (j : J) (S : G .E → J) →
   Realize (graph/ (G .V) (⋆ S ⊞ jbar j) (⊞e ((G .b) ∘ 𝕖 S) (λ _ → ∂))) ≡
   Realize (graph/ (contractTypeBy (G .V) ∂ (jbar j)) (⋆ S) (square inject ∘ (G .b) ∘ 𝕖 S))
 RG2=RG3 {G} {∂} j S = RG2=RG3-lemma {G .V} {jbar j} {∂} (⋆ S) (G .b ∘ 𝕖 S)

 RG1=RG3 : {G : Graph} {∂ : GBd G} (j : J) (S : G .E → J) →
   Realize (FromGraph.G1 G ∂ j S) ≡ Realize (FromGraph.G3 G ∂ j S)
 RG1=RG3 {G} {∂} j S = (λ i → Realize (G1=G2 {G} {∂} j S i)) ∙ RG2=RG3 j S

module GraphLemma {X Y : Set} (G : Graph) (∂ : GBd G)   where
 open FromGraph G ∂
 open Graph

 module _ (j : J) (S : (Graph.E G) → J) where
   graph-lemma : ((E1 j S → Y) × (Realize (G1 j S) → X))
              ≡ ((⋆ S ⊞ jbar j → Y) × ((Realize (G3 j S)) → X))
   graph-lemma i = (E1=E2 j S i → Y) × ( (RG1=RG3 {G} {∂} j S i) → X)

sum-lemma1 : {A B C : Set} → ((A ⊞ B) → C) ≡ ((B → C) × (A → C))
sum-lemma1 {A} {B} {C} = ua (isoToEquiv (iso fore back crefl back-fore)) where
 fore : (A ⊞ B → C) → (B → C) × (A → C)
 fore f = (f ∘ Inr) , (f ∘ Inl)

 back : (B → C) × (A → C) → ((A ⊞ B) → C)
 back (g , f) (Inl x) = f x
 back (g , f) (Inr x) = g x

 back-fore : section back fore
 back-fore b i (Inl x) = b (Inl x)
 back-fore b i (Inr x) = b (Inr x)

sum-lemma2 : (A B : Set) (P : A → Set) (Q : B → Set) (R : A → B → Set) →
   (Σ A \ a → Σ B λ b → (P a × Q b) × R a b)
     ≡
   (Σ A \ a → P a × Σ B λ b → Q b × R a b)
sum-lemma2 A B P Q R = ua (isoToEquiv (iso fore back crefl crefl)) where
 T1 = (Σ A \ a → Σ B λ b → (P a × Q b) × R a b)
 T2 = (Σ A \ a → P a × Σ B λ b → Q b × R a b)

 fore : T1 → T2
 fore (a , b , (p , q) , r) = a , (p , (b , (q , r)))

 back : T2 → T1
 back (a , (p , (b , (q , r)))) = (a , b , (p , q) , r)
