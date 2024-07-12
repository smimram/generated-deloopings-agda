{-

  This file contains:

  - Definition of GSet Homomorphisms
  - Definition of GSetEquiv : GSet Isomorphisms

-}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
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

  -- Morphisms of G-sets
  GSetHom : (X Y : GSet G) → Type ℓ
  GSetHom X Y = Σ[ f ∈ (⟨ X ⟩ → ⟨ Y ⟩) ] IsGSetHom (str X) f (str Y)

  -- Predicate of being a morphism of G-sets for equivalences
  isGSetEquiv : {X Y : Type ℓ} (M : GSetStr G X) (N : GSetStr G Y) (e : X ≃ Y) → Type ℓ
  isGSetEquiv M N e = IsGSetHom M (e .fst) N

  -- Equivalences of G-sets
  GSetEquiv : (X Y : GSet G) → Type ℓ
  GSetEquiv X Y = Σ[ e ∈ (⟨ X ⟩ ≃ ⟨ Y ⟩) ] isGSetEquiv (str X) (str Y) e

  makeIsGSetEquiv = makeIsGSetHom

  isPropIsGSetHom : {X Y : GSet G} {f : ⟨ X ⟩ → ⟨ Y ⟩} → isProp (IsGSetHom (str X) f (str Y))
  isPropIsGSetHom {X = X} {Y = Y} = isOfHLevelRespectEquiv 1 (invEquiv (isoToEquiv IsGSetHomIsoΣ)) (isPropΠ2 λ g x → ((str Y) .GSetStr.is-set) _ _)

  GSetIdEquiv : (X : GSet G) → GSetEquiv X X
  GSetIdEquiv X = idEquiv ⟨ X ⟩ , makeIsGSetEquiv λ x y → refl

  idToGSetEquiv' : {X Y : GSet G} → X ≡ Y → GSetEquiv X Y
  idToGSetEquiv' {X = X} {Y = Y} = J (λ Y p → GSetEquiv X Y) (GSetIdEquiv X)

  idToGSetIdEquivRefl' : {X : GSet G} → idToGSetEquiv' refl ≡ GSetIdEquiv X
  idToGSetIdEquivRefl' {X = X} = JRefl (λ Y p → GSetEquiv X Y) (GSetIdEquiv X)

  -- The underlying equivalence of idToGSetEquiv is pathToEquiv
  idToGSetEquiv'Fst : {X Y : GSet G} (p : X ≡ Y) → fst (idToGSetEquiv' p) ≡ pathToEquiv (cong fst p)
  idToGSetEquiv'Fst {X} {Y} = J (λ Y p → fst (idToGSetEquiv' p) ≡ pathToEquiv (cong fst p)) lem
    where
    lem =
      fst (idToGSetEquiv' {X = X} refl) ≡⟨ cong fst (idToGSetIdEquivRefl' {X = X}) ⟩
      fst (GSetIdEquiv X)              ≡⟨ sym pathToEquivRefl ⟩
      pathToEquiv (refl {x = fst X})   ≡⟨ refl ⟩
      pathToEquiv (cong fst (refl {x = X})) ∎

  -- Variant with function X → Y being definitionaly pathToEquiv
  idToGSetEquiv : {X Y : GSet G} → X ≡ Y → GSetEquiv X Y
  idToGSetEquiv {X = X} p = pathToEquiv (cong fst p) , subst (isGSetEquiv _ _) (idToGSetEquiv'Fst p) (snd (idToGSetEquiv' p))

  idToGSetEquivFst : {X Y : GSet G} (p : X ≡ Y) → fst (idToGSetEquiv p) ≡ pathToEquiv (cong fst p)
  idToGSetEquivFst p = refl

  -- Two equivalences of G-sets can be compared by comparing the underlying functions
  GSetEquiv≡ : {X Y : GSet G} {f g : GSetEquiv X Y} → equivFun (fst f) ≡ equivFun (fst g) → f ≡ g
  GSetEquiv≡ p = Σ≡Prop (λ _ → isPropIsGSetHom) (Σ≡Prop isPropIsEquiv p)
