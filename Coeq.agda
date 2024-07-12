{-# OPTIONS --cubical #-}

module Coeq where

-- The standard library unfortunately does not have coequalisers. Add them.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

private variable
  ℓ ℓ' ℓ'' : Level

module _ {A : Type ℓ} {B : Type ℓ'} (f g : A → B) where

  -- Coequalizer of two maps
  data Coeq : Type (ℓ-max ℓ ℓ') where
    incl : (b : B) → Coeq
    coeq : (a : A) → incl (f a) ≡ incl (g a)

  -- Elimination principle for coequalizers
  elim : (C : Coeq → Type ℓ'') (Ci : (b : B) → C (incl b)) (Ce : (a : A) → PathP (λ i → cong C (coeq a) i) (Ci (f a)) (Ci (g a))) (x : Coeq) → C x
  elim C Ci Ce (incl b) = Ci b
  elim C Ci Ce (coeq a i) = Ce a i

module _ {A A' : Type ℓ} {B B' : Type ℓ'} (f g : A → B) (f' g' : A' → B') where
  record CoeqHom : Type (ℓ-max ℓ ℓ') where
    field
      hom-incl : B → B'
      hom-coeq : A → A'
      hom-f    : (a : A) → hom-incl (f a) ≡ f' (hom-coeq a)
      hom-g    : (a : A) → hom-incl (g a) ≡ g' (hom-coeq a)

  open CoeqHom

  -- Morphism induced by a morphism of coequalizer diagrams.
  CoeqHom→ : CoeqHom → Coeq f g → Coeq f' g'
  CoeqHom→ ϕ (incl b) = incl (ϕ .hom-incl b)
  CoeqHom→ ϕ (coeq a i) = lem i
    where
    hA = ϕ .hom-coeq
    hB = ϕ .hom-incl
    lem : incl (hB (f a)) ≡ incl (hB (g a))
    lem =
      incl (hB (f a))  ≡⟨ cong incl (ϕ .hom-f a) ⟩
      incl (f' (hA a)) ≡⟨ coeq (hA a) ⟩
      incl (g' (hA a)) ≡⟨ sym (cong incl (ϕ .hom-g a)) ⟩
      incl (hB (g a))  ∎

  CoeqEquiv : Type (ℓ-max ℓ ℓ')
  CoeqEquiv = Σ CoeqHom λ h → isEquiv (h .hom-incl) × isEquiv (h .hom-coeq)

-- module _ {A A' : Type ℓ} {B B' : Type ℓ'} (f g : A → B) (f' g' : A' → B') where
  -- CoeqInvEquiv : CoeqEquiv f g f' g' → CoeqEquiv f' g' f g
  -- CoeqInvEquiv (h , hBe , hAe) = k , {!!} , {!!}
    -- where
    -- open CoeqHom
    -- k : CoeqHom f' g' f g
    -- hom-incl k = invEq (_ , hBe)
    -- hom-coeq k = invEq (_ , hAe)
    -- hom-f k a = {!invEq (h .hom-incl , hBe) (f' a) ≡
      -- f (invEq (h .hom-coeq , hAe) a) ∎!}
    -- hom-g k = {!!}

  postulate
    -- Assuming this classical result: an isomorphism of coequalizer diagrams
    -- induces an insomorphism between the corresponding coequalizers.
    Coeq≃ : CoeqEquiv → Coeq f g ≃ Coeq f' g'
