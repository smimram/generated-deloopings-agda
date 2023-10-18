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

  ι-star-hom : GroupHom (freeGroupGroup ⟨ X ⟩) G
  ι-star-hom = Cubical.HITs.FreeGroup.rec ι

  ι-star : FreeGroup ⟨ X ⟩  → ⟨ G ⟩
  ι-star = fst ι-star-hom

  ι-generates = isSurjective ι-star-hom
