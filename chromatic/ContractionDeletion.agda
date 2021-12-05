{-# OPTIONS --without-K --rewriting --cubical #-}

module chromatic.ContractionDeletion where
open import Util

open import chromatic.Defns
open import chromatic.ChromaticLemmas

contraction-deletion : (G : Graph) (∂ : GBd G) (X Y : Set) →
   Chromatic (withEdge G ∂) X Y ≡ Σ J \ j → (jbar j → Y) × Chromatic (contractEdgeJ G ∂ j) X Y

contraction-deletion G ∂ X Y =
   Chromatic (withEdge G ∂) X Y
    ≡⟨ refl ⟩
   (Σ (Subgraph (withEdge G ∂)) λ S → Contrib (restrict (withEdge G ∂) S) X Y)
     ≡⟨ refl ⟩
   (Σ (Subgraph (withEdge G ∂)) λ S → Contrib (graph/ ((withEdge G ∂) .V) (⋆ S) ((withEdge G ∂) .b ∘ 𝕖 S)) X Y)
      ≡⟨ refl ⟩
   (Σ (Subgraph (withEdge G ∂)) λ S → Contrib (G0 S) X Y)
      ≡⟨ refl ⟩
   (Σ (Maybe (G .E) → J) λ S → Contrib (G0 S) X Y)
      ≡⟨ refl ⟩
   (Σ (Maybe (G .E) → J) λ S → (⋆ S → Y) × (Realize (G0 S) → X))
     ≡⟨ maybe-lemma {G .E} {J} {λ S → (⋆ S → Y) × (Realize (G0 S) → X)} ⟩
   (Σ J \ j → Σ ((G .E) → J) λ S → (E1 j S → Y) × (Realize (G1 j S) → X))
     ≡⟨ (λ i → Σ J \ j → Σ ((G .E) → J) λ S → GraphLemma.graph-lemma {X} {Y} G ∂ j S i) ⟩
   (Σ J \ j → Σ ((G .E) → J) λ S → (⋆ S ⊞ jbar j → Y) × (Realize (G3 j S) → X))
     ≡⟨ (λ i → (Σ J \ j → Σ ((G .E) → J) λ S → sum-lemma1 {⋆ S} {jbar j} {Y} i × (Realize (G3 j S) → X))) ⟩
   (Σ J \ j → Σ ((G .E) → J) λ S → ((jbar j → Y) × (⋆ S → Y)) × (Realize (G3 j S) → X))
     ≡⟨ sum-lemma2 J (G .E → J) (λ j → jbar j → Y) (λ S → ⋆ S → Y) (λ j S → Realize (FromGraph.G3 G ∂ j S) → X) ⟩
   (Σ J \ j → (jbar j → Y) × Σ ((G .E) → J) λ S → (⋆ S → Y) × ((Realize (G3 j S)) → X))
     ≡⟨ refl ⟩
   (Σ J \ j → (jbar j → Y) × Σ ((G .E) → J) λ S → Contrib (G3 j S) X Y)
     ≡⟨ refl ⟩
   (Σ J \ j → (jbar j → Y) × Σ ((G .E) → J) λ S → Contrib (restrict (contractEdgeJ G ∂ j) S) X Y)
     ≡⟨ refl ⟩
   (Σ J \ j → (jbar j → Y) × Σ (Subgraph (contractEdgeJ G ∂ j)) λ S → Contrib (restrict (contractEdgeJ G ∂ j) S) X Y)
     ≡⟨ refl ⟩
   (Σ J \ j → (jbar j → Y) × Chromatic (contractEdgeJ G ∂ j) X Y)
     ∎ where
  open FromGraph G ∂
  open Graph
