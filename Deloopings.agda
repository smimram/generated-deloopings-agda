{-

  This file contains:

  - Delooping by torsors (classical construction and proof)
  - Delooping by generated torsors

  -}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.FreeGroup renaming (_·_ to _·f_)
open import Cubical.Homotopy.Group.Base

open import XSet
open import GSet
open import GSetProperties
open import Generators
open import XSetProperties
open import Comp
open import PrincipalTorsor


private
  variable
    ℓ : Level

module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  open generators {G = G} {X = X} {ι = ι}
  open principal-torsor
  module _ {gen : ι-generates} where
  BG : Pointed (ℓ-suc ℓ)
  BG = Comp (GSet ℓ G , PG)

  PX : XSet ℓ X
  PX = U {G = G} {ι = ι} PG

  BG' : Pointed (ℓ-suc ℓ)
  BG' = Comp (XSet ℓ X , PX)

  PG=PGisoG : (πGr 0 BG) ≡ G
  PG=PGisoG = ?
