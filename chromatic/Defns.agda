{-# OPTIONS --without-K --rewriting --cubical #-}

module chromatic.Defns where
open import Util

{- the point of this file is to replace subgraphs E → 2 with a more
   general E → J for some index set J with fibered π : Q → J which
   hopefully might go down easier. -}

record Graph : Set₁ where
 constructor graph/
 field
  V E : Set
  b : E → V × V

module _ where
 open Graph

 postulate
  J Q : Set
  π : Q → J

 hfib : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (f : A → B) (b : B) → Set (ℓA ⊔ ℓB)
 hfib {A = A} f b = Σ A (λ a → f a ≡ b)

 jbar : J → Set
 jbar j = hfib π j

 Subgraph : Graph → Set
 Subgraph (graph/ V E b) = E → J

 ⋆ : {E : Set} (f : E → J) → Set
 ⋆ {E} f = Σ (E × Q) (λ (e , q) → π q ≡ f e)

 𝕖 : {E : Set} (S : E → J) → ⋆ S → E
 𝕖 S (( e , q ) , p ) = e

 restrict : (G : Graph) → Subgraph G → Graph
 restrict G S = graph/ (G .V) (⋆ S) (G .b ∘ 𝕖 S)

 data Realize (G : Graph) : Set where
   ri : G .V → Realize G
   rp : (e : G .E) → ri (fst (G .b e)) ≡ ri (snd (G .b e))

 Contrib : (G : Graph) (X Y : Set) → Set
 Contrib G X Y = (G .E → Y) × (Realize G → X)

 Chromatic : (G : Graph) (X Y : Set) → Set
 Chromatic G X Y = Σ (Subgraph G) λ S → Contrib (restrict G S) X Y

 -- an edge boundary in a type is a pair of points
 Bd : Set → Set
 Bd V = V × V

 -- an edge boundary in a graph is a pair of vertices
 GBd : Graph → Set
 GBd (graph/ V E b) = Bd V

 -- take a type and add paths to it between two points
 data contractTypeBy (V : Set) (∂ : Bd V) (Φ : Set) : Set where
   inject : V → contractTypeBy V ∂ Φ
   theyre-equal : (φ : Φ) → inject (fst ∂) ≡ inject (snd ∂)

 liftm : {E V : Set} (bd : E → V) (v : V) → Maybe E → V
 liftm bd v (Just e) = bd e
 liftm bd v None = v

 -- take a graph and add an edge to it
 withEdge : (G : Graph) (∂ : GBd G) → Graph
 withEdge (graph/ V E b) ∂ =  graph/ V (Maybe E) (liftm b ∂)

 square : {X Y : Set} (f : X → Y) → (X × X) → (Y × Y)
 square f (x1 , x2) = (f x1 , f x2)

 -- take a graph and add a path between vertices
 contractEdgeJ : (G : Graph) (∂ : GBd G) (j : J) → Graph
 contractEdgeJ (graph/ V E b) ∂ j = graph/ (contractTypeBy V ∂ (jbar j)) E (square inject ∘ b)
