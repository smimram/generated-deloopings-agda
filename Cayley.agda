{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.HITs.EilenbergMacLane1 as EM
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening

open import Generators

private variable
  ℓ ℓ' ℓ'' : Level

-- data Coeq {A : Type ℓ} {B : Type ℓ'} (f g : A → B) : Type (ℓ-max ℓ ℓ') where
  -- incl : B → Coeq f g
  -- coeq : (a : A) → incl (f a) ≡ incl (g a)

-- -- Flattening for coequalizers
-- flattenCoeq : {A : Type ℓ} {B : Type ℓ'} (f g : A → B) (F : Coeq f g → Type ℓ'') → Σ (Coeq f g) F ≃ Coeq {!!} {!!}
-- flattenCoeq = {!!}

module _ {G : Group ℓ} {X : hSet ℓ} (γ : ⟨ X ⟩ → ⟨ G ⟩) (gen : generates {X = X} {G = G} γ) where
  open GroupStr (str G)

  data BX* : Set ℓ where
    base : BX*
    loop : ⟨ X ⟩ → base ≡ base

  Bγ* : BX* → EM₁ G
  Bγ* base = embase
  Bγ* (loop x i) = emloop (γ x) i

  data Cayley : Type ℓ where
    vertex : ⟨ G ⟩ → Cayley
    edge : (g : ⟨ G ⟩) (x : ⟨ X ⟩) → vertex g ≡ vertex (g · γ x)

  Cayley-ker : Cayley ≃ Σ BX* (λ x → embase ≡ Bγ* x)
  Cayley-ker = {!!}
    where
    f : ?
    f = ?
    flat : {!!}
    flat = FlatteningLemma.flatten {!!} {!!} {!!} {!!} {!!}
