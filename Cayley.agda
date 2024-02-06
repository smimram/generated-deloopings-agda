{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.EilenbergMacLane1 as EM
open import Cubical.HITs.Pushout

open import Generators

private variable
  ℓ ℓ' ℓ'' : Level

data Coeq {A : Type ℓ} {B : Type ℓ'} (f g : A → B) : Type (ℓ-max ℓ ℓ') where
  incl : B → Coeq f g
  coeq : (a : A) → incl (f a) ≡ incl (g a)

-- Flattening for coequalizers
module FlatteningLemma {A : Type ℓ} {B : Type ℓ'} (f g : A → B) (P : B → Type ℓ'') (p : (a : A) → P (f a) ≡ P (g a)) where
  P' : Coeq f g → Type ℓ''
  P' (incl x) = P x
  P' (coeq a i) = p a i

  ΣAP = Σ A (P ∘ f)

  Σf : ΣAP → Σ B P
  Σf (a , x) = f a , x

  Σg : ΣAP → Σ B P
  Σg (a , x) = g a , transport (p a) x

  postulate
    -- See the HoTT book, section 6.12
    flatten : Σ (Coeq f g) P' ≃ Coeq Σf Σg

module _ {G : Group ℓ} {X : hSet ℓ} (γ : ⟨ X ⟩ → ⟨ G ⟩) (gen : generates {X = X} {G = G} γ) where
  open GroupStr (str G)

  data BX* : Set ℓ where
    base : BX*
    loop : ⟨ X ⟩ → base ≡ base

  Bγ* : BX* → EM₁ G
  Bγ* base = embase
  Bγ* (loop x i) = emloop (γ x) i

  data Cayley : Type ℓ where
    vertex : ⟨ G ⟩ → Cayley
    edge   : (g : ⟨ G ⟩) (x : ⟨ X ⟩) → vertex g ≡ vertex (g · γ x)

  Cayley-ker : Cayley ≃ Σ BX* (λ x → embase ≡ Bγ* x)
  Cayley-ker =
    Cayley                       ≃⟨ Cayley≃Σ ⟩
    Coeq Σf Σg                   ≃⟨ invEquiv flatten ⟩
    Σ (Coeq f g) P'              ≃⟨ Σ-cong-equiv (invEquiv (BX*≃Coeq)) equiv ⟩
    Σ BX* (λ x → embase ≡ Bγ* x) ■
    where
    f : ⟨ X ⟩ → Unit
    f _ = tt
    g = f

    open FlatteningLemma f g (λ _ → base ≡ base) (λ a → ua (compPathrEquiv (loop a)))

    Cayley≃Σ : Cayley ≃ Coeq Σf Σg
    Cayley≃Σ = isoToEquiv e
      where
      open Iso
      e : Iso Cayley (Coeq Σf Σg)
      fun e (vertex x) = incl (tt , (loop {!!}))
      fun e (edge u x i) = {!!}
      inv e x = {!!}
      rightInv e x = {!!}
      leftInv e x = {!!}

    BX*→Coeq : BX* → Coeq f g
    BX*→Coeq base = incl tt
    BX*→Coeq (loop x i) = coeq x i

    Coeq→BX* : Coeq f g → BX*
    Coeq→BX* (incl tt) = base
    Coeq→BX* (coeq x i) = loop x i

    -- Direct isomorphism
    BX*≃Coeq : BX* ≃ Coeq f g
    BX*≃Coeq = isoToEquiv e
      where
      open Iso
      e : Iso BX* (Coeq f g)
      fun e = BX*→Coeq
      inv e = Coeq→BX*
      rightInv e (incl x) = refl
      rightInv e (coeq x i) = refl
      leftInv e base = refl
      leftInv e (loop x i) = refl
    equiv : (x : Coeq f g) →  FlatteningLemma.P' f g (λ _ → base ≡ base) (λ a → ua (compPathrEquiv (loop a))) x ≃ (embase ≡ Bγ* (Coeq→BX* x))
    equiv (incl x) = isoToEquiv {!!}
      where
      open Iso
      e : Iso (base ≡ base) (embase ≡ embase)
      fun e p = {!!}
      inv e = {!!}
      rightInv e = {!!}
      leftInv e = {!!}
    equiv (coeq x i) = {!!}
