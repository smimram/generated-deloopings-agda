{-

  This file contains:

  - Definition of Group generation

-}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.HITs.FreeGroup as FG
open import Cubical.HITs.PropositionalTruncation as PT

open import XSet
open import GSet

private
  variable
    ℓ : Level

module _ {X : hSet ℓ} {G : Group ℓ} (γ : ⟨ X ⟩ → ⟨ G ⟩) where

  -- Group morphism X* → G induced by γ : X → G
  freeGHom : GroupHom (freeGroupGroup ⟨ X ⟩) G
  freeGHom = FG.rec γ

  -- The fact that X generates G (through γ)
  generates : Type ℓ
  generates = isSurjective freeGHom

  -- Strong generation: γ admits a section
  strongly-generates : Type ℓ
  strongly-generates = Σ (⟨ G ⟩ → freeGroupGroup ⟨ X ⟩ .fst) (λ σ → (g : ⟨ G ⟩) → freeGHom .fst (σ g) ≡ g)

  -- Strong generation implies generation
  sg-g : strongly-generates → generates
  sg-g (f , sec) g = ∣ f g , sec g ∣₁
