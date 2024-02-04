{-

  This file contains:

  - Definition of Group generation

-}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.HITs.FreeGroup as FG

open import XSet
open import GSet

private
  variable
    ℓ : Level

module _ {X : hSet ℓ} {G : Group ℓ} (γ : ⟨ X ⟩ → ⟨ G ⟩) where

  -- Group morphism X* → G induced by ι : X → G
  freeGHom : GroupHom (freeGroupGroup ⟨ X ⟩) G
  freeGHom = FG.rec γ

  -- The fact that X generates G (through ι)
  generates : Type ℓ
  generates = isSurjective freeGHom
