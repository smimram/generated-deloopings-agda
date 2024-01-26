{-

  This file contains:

  - Definition of Group generation

-}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.HITs.FreeGroup

open import XSet
open import GSet

private
  variable
    ℓ : Level

module generators {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where

  -- Group morphism X* → G induced by ι : X → G
  ι-star-hom : GroupHom (freeGroupGroup ⟨ X ⟩) G
  ι-star-hom = Cubical.HITs.FreeGroup.rec ι

  -- Underlying morphism of the above group morphism
  ι-star : FreeGroup ⟨ X ⟩  → ⟨ G ⟩
  ι-star = fst ι-star-hom

  -- The fact that X generates G (through ι)
  ι-generates : Type ℓ
  ι-generates = isSurjective ι-star-hom
