{-

  This file contains:

  - Definition of the principal torsor of a group

  -}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.FreeGroup renaming (_·_ to _·f_)

open import GSet
open import GSetProperties

-- The principal G-torsor
Principal : {ℓ : Level} (G : Group ℓ) → GSet G
Principal {ℓ} G = ⟨ G ⟩ , gsetstr a
  where
  open GroupStr (str G)
  a : Action {ℓ} G ⟨ G ⟩
  a = record {
    _*_ = _·_ ;
    is-set = is-set ;
    ·Unit = ·IdL ;
    ·Composition = ·Assoc
    }
