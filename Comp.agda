{-

  This file contains:

  - Definition of Comp the connected component of a pointed space (A, a0)
  - Definition of the fundamental group π₁ for groupoids
  - The Comp of a groupoid is a groupoid
  - π₁(Comp(A, a0)) = π₁(A,a0)

-}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Foundations.GroupoidLaws as GL

private
  variable
    ℓ : Level

-- The connected component of a pointed space
Comp : Pointed ℓ → Pointed ℓ
Comp X = Σ ⟨ X ⟩ (λ x  → ∥ (pt X) ≡ x ∥₁), (pt X , ∣ refl ∣₁)

-- Connectedness of a type
isConnected : Type ℓ → Type ℓ
isConnected A = isContr ∥ A ∥₂

-- The connected component is connected
isConnectedComp : (A : Pointed ℓ) → isConnected ⟨ Comp A ⟩
isConnectedComp A = ∣ pt A , ∣ refl ∣₁ ∣₂ , ST.elim (λ x → isSet→isGroupoid isSetSetTrunc _ _) (λ x → PathIdTrunc₀Iso .Iso.inv (PT.elim (λ _ → isPropPropTrunc { A = _ ≡ x }) (λ p → ∣ ΣPathP (p , toPathP (isPropPropTrunc _ _)) ∣₁) (snd x)))

-- The canonical map Comp A → A is an embedding
PathComp : {A : Pointed ℓ} (x y : ⟨ Comp A ⟩) → (x ≡ y) ≃ (fst x ≡ fst y)
PathComp x y = isoToEquiv e
  where
  open Iso
  e : Iso (x ≡ y) (fst x ≡ fst y)
  fun e p = cong fst p
  inv e p = ΣPathP (p , (toPathP (isPropPropTrunc _ _)))
  rightInv e p = refl
  leftInv e p = isoFunInjective (equivToIso (invEquiv (Σ≡PropEquiv (λ _ → isPropPropTrunc))))  _ _ refl

-- The fundamental group of a groupoid
π₁ : (A : Pointed ℓ) → isGroupoid ⟨ A ⟩ → Group ℓ
π₁ A gpd = (pt A ≡ pt A) , grp
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

-- The connected component of a groupoid is a groupoid
groupoidComp : (A : Pointed ℓ) → isGroupoid ⟨ A ⟩ → isGroupoid ⟨ Comp A ⟩
groupoidComp A gpd = isGroupoidΣ gpd λ x → isOfHLevelPlus {n = 1} 2 isPropPropTrunc

-- Taking connected components preserves loop spaces
loopCompIsLoop : {A : Pointed ℓ} → Ω (Comp A) ≃∙ Ω A
loopCompIsLoop {ℓ} {A} = PathComp _ _ , refl

-- The fundamental groupoid is preserved by taking the component
π₁Comp : (A : Pointed ℓ) (gpd : isGroupoid ⟨ A ⟩) → GroupIso (π₁ (Comp A) (groupoidComp A gpd)) (π₁ A gpd)
π₁Comp A gpd = equivToIso (PathComp _ _) , record {
  pres· = λ p q → cong fst (p ∙ q) ≡⟨ cong-∙ fst p q ⟩ (cong fst p) ∙ (cong fst q) ∎;
  pres1 = refl;
  presinv = λ x → refl
  }
