{-# OPTIONS --cubical #-}

---
--- Embeddings and applications.
---

open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.Algebra.Group

open import Generators

private variable
  ℓ ℓ' : Level

module _ (G : Group ℓ) (X : hSet ℓ) (γ : ⟨ X ⟩ → ⟨ G ⟩) (gen : generates {X = X} {G = G} γ) where
  
