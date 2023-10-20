{-

  This file contains:

  - Definition of Comp the connected component of a pointed space (A, a0)
  - Ω(Comp(A, a0)) = Ω(A,a0)

-}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Everything
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Sigma
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level

-- Definition of the connected component of a pointed space
Comp : Pointed ℓ → Pointed ℓ
Comp X = Σ ⟨ X ⟩ (λ x  → ∥ (pt X) ≡ x ∥₁), (pt X , ∣ refl ∣₁)

PathComp : {A : Pointed ℓ} (x y : ⟨ Comp A ⟩) → (x ≡ y) ≃ (fst x ≡ fst y)
PathComp x y = isoToEquiv e
  where
  open Iso
  e : Iso (x ≡ y) (fst x ≡ fst y)
  fun e p = cong fst p
  inv e p = ΣPathP (p , (toPathP (isPropPropTrunc _ _)))
  rightInv e p = refl
  leftInv e p = isoFunInjective (equivToIso (invEquiv (Σ≡PropEquiv (λ _ → isPropPropTrunc))))  _ _ refl

loopCompIsLoop : {A : Pointed ℓ} → Ω (Comp A) ≃∙ Ω A
loopCompIsLoop {ℓ} {A} = PathComp _ _ , refl
