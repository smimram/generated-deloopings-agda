{-

  This file contains:

  - Definition of the principal torsor of a group
  - Caracterisation of its Aut group

  -}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.FreeGroup renaming (_·_ to _·f_)

open import GSet
open import GSetProperties

private
  variable
    ℓ : Level

module principal-torsor {G : Group ℓ} where
  open GroupStr (str G)
  left-action : Action {ℓ} G ⟨ G ⟩
  left-action = record {
    _*_ = _·_ ;
    is-set = is-set ;
    ·Unit = ·IdL ;
    ·Composition = ·Assoc
    }

  PG : GSet ℓ G
  PG = ⟨ G ⟩ , gsetstr left-action
