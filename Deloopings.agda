{-

  This file contains:

  - Delooping by torsors (classical construction and proof)
  - Delooping by generated torsors

  -}

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
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

--- fundamental group of a groupoid
π₁ : {A : Pointed ℓ} → isGroupoid ⟨ A ⟩ → Group ℓ
π₁ {A = A} gpd = (pt A ≡ pt A) , grp
  where
  open GroupStr
  open IsSemigroup
  open IsMonoid
  open IsGroup
  grp : GroupStr (pt A ≡ pt A)
  1g grp = refl
  _·_ grp p q = p ∙ q
  GroupStr.inv grp p = sym p
  is-set (isSemigroup (isMonoid (isGroup grp))) = gpd (pt A) (pt A)
  ·Assoc (isSemigroup (isMonoid (isGroup grp))) = GL.assoc
  ·IdR (isMonoid (isGroup grp)) p = sym (rUnit p)
  ·IdL (isMonoid (isGroup grp)) p = sym (lUnit p)
  ·InvR (isGroup grp) = rCancel
  ·InvL (isGroup grp) = lCancel

module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  open generators {G = G} {X = X} {ι = ι}
  open principal-torsor
  module _ {gen : ι-generates} where
  BG : Pointed (ℓ-suc ℓ)
  BG = Comp (GSet G , PG)

  isGroupoidBG : isGroupoid ⟨ BG ⟩
  isGroupoidBG f g = subst isSet (sym (ua (PathComp f g))) {!str X!}

  PX : XSet X
  PX = U {G = G} {ι = ι} PG

  BG' : Pointed (ℓ-suc ℓ)
  BG' = Comp (XSet X , PX)

  PG=PGisoG : GroupIso (π₁ {A = BG} {!!}) G
  PG=PGisoG = {!!}
