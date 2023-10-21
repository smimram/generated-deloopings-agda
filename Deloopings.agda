{-

  This file contains:

  - Delooping by torsors (classical construction and proof)
  - Delooping by generated torsors
  - Caracterisation of the Principal torsor's Aut group

  -}

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Univalence
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.FreeGroup renaming (_·_ to _·f_)
open import Cubical.Homotopy.Group.Base

open import XSet
open import GSet
open import GSetHom
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
  BG = Comp (GSet G , PG)

  isGroupoidBG : isGroupoid ⟨ BG ⟩
  isGroupoidBG = groupoidComp (GSet G , PG) (isGroupoidGSet G)

  PX : XSet X
  PX = U {G = G} {ι = ι} PG

  BG' : Pointed (ℓ-suc ℓ)
  BG' = Comp (XSet X , PX)

  PGloops : GroupIso (π₁ (GSet G , PG) (isGroupoidGSet G)) G
  PGloops = e , {!!}
    where
    open Iso
    open GroupStr (str G)
    m≃ : ⟨ G ⟩ → GSetEquiv (PG {G = G}) PG
    m≃ x = (isoToEquiv e , makeIsGSetEquiv {G = G} λ y z → sym (·Assoc _ _ _))
      where
      e : Iso ⟨ PG {G = G} ⟩ ⟨ PG {G = G} ⟩
      fun e y = y · x
      Iso.inv e y = y · GroupStr.inv (str G) x
      rightInv e y = sym (·Assoc _ _ _) ∙ cong (λ x → y · x) (·InvL x) ∙ ·IdR y
      leftInv e y = sym (·Assoc _ _ _) ∙ cong (λ x → y · x) (·InvR x) ∙ ·IdR y
    m : ⟨ G ⟩ → PG {G = G} ≡ PG
    m x = GSetUA (m≃ x)
    mTr : (x y : ⟨ G ⟩) → subst fst (m x) y ≡ y · x
    mTr x y = {!!} ∙ uaβ (fst (m≃ x)) y
    e : Iso (PG ≡ PG) ⟨ G ⟩
    fun e p = transport (cong fst p) 1g
    Iso.inv e x = m x
    rightInv e x = mTr x 1g ∙ ·IdL x
    leftInv e p = cong m {!!} ∙ {!!}

  torsorDeloops : GroupIso (π₁ BG isGroupoidBG) G
  torsorDeloops = compGroupIso {G = π₁ BG isGroupoidBG} (π₁Comp (GSet G , PG) (isGroupoidGSet G)) PGloops
