{-

  This file contains:

  - Definition of GSet Homomorphisms
  - Definition of GSetEquiv : GSet Isomorphisms

-}

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Reflection.RecordEquiv

open import GSet

private
  variable
    ℓ : Level

-- TODO: can the Levels be different ?
record IsGSetHom {G : Group ℓ} {X Y : Type ℓ} (M : GSetStr G X)  (f : X → Y) (N : GSetStr G Y)
  : Type ℓ
  where

  -- shorter qualified names
  private
    module M = GSetStr M
    module N = GSetStr N

  field
    pres* : (g : ⟨ G ⟩) (x : X ) → f (g M.* x) ≡ g N.* (f x)

unquoteDecl IsGSetHomIsoΣ = declareRecordIsoΣ IsGSetHomIsoΣ (quote IsGSetHom)

module _ {G : Group ℓ} {X : Type ℓ} {Y : Type ℓ} {M : GSetStr {ℓ} G X} {f : X → Y} {N : GSetStr {ℓ} G Y}
  (pres : (g : ⟨ G ⟩) (x : X) → f ((GSetStr._*_ M) g x) ≡ (GSetStr._*_ N) g (f x))
  where

  makeIsGSetHom : IsGSetHom M f N
  makeIsGSetHom .IsGSetHom.pres* = pres

module _ {G : Group ℓ} where

  GSetHom : (X Y : GSet G) → Type ℓ
  GSetHom X Y = Σ[ f ∈ (⟨ X ⟩ → ⟨ Y ⟩) ] IsGSetHom (str X) f (str Y)

  IsGSetEquiv : {X Y : Type ℓ} (M : GSetStr G X) (e : X ≃ Y) (N : GSetStr G Y) → Type ℓ
  IsGSetEquiv M e N = IsGSetHom M (e .fst) N

  GSetEquiv : (X Y : GSet G) → Type ℓ
  GSetEquiv X Y = Σ[ e ∈ (⟨ X ⟩ ≃ ⟨ Y ⟩) ] IsGSetEquiv (str X) e (str Y)

  makeIsGSetEquiv = makeIsGSetHom

  GSetIdEquiv : (X : GSet G) → GSetEquiv X X
  GSetIdEquiv X = idEquiv ⟨ X ⟩ , makeIsGSetEquiv λ x y → refl

  idToGSetEquiv : {X Y : GSet G} → X ≡ Y → GSetEquiv X Y
  idToGSetEquiv {X = X} = J (λ Y p → GSetEquiv X Y) (GSetIdEquiv X)

  GSetUnivalence : {X Y : GSet G} → isEquiv (idToGSetEquiv {X = X} {Y = Y})
  GSetUnivalence = {!!}

  GSetUA : {X Y : GSet G} → GSetEquiv X Y → X ≡ Y
  GSetUA {X} {Y} = invEq (_ , GSetUnivalence {X = X} {Y = Y})
