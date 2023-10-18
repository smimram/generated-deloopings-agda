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
Comp X = ( Σ ⟨ X ⟩ (λ x  → ∥ (pt X) ≡ x ∥₁), (pt X , ∣ refl ∣₁) )

loopCompIsLoop : {A : Pointed ℓ} → Ω (Comp A) ≃∙ Ω A
loopCompIsLoop {ℓ} {A} = isoToEquiv e , refl
  where
  e : Iso (fst (Ω (Comp A))) (fst (Ω A))

  -- On projete ((a0, _) ≡ (a0,_)) sur (a0 ≡ a0)
  Iso.fun e p = cong fst p

  -- Pour retourner en arrière on remarque qu'il n'y a qu'un témoin de (∥ x ≡ y ∥₁)
  Iso.inv e p = ΣPathP (p , toPathP (isPropPropTrunc _ _))

  Iso.rightInv e p = refl
  Iso.leftInv e p = isoFunInjective (equivToIso (invEquiv (Σ≡PropEquiv (λ _ → isPropPropTrunc))))  _ _ refl
