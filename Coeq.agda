{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Coeq where

open import Cubical.Foundations.Everything
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

  CoeqHom→ : CoeqHom → Coeq f g → Coeq f' g'
  CoeqHom→ ϕ (incl b) = incl (ϕ .hom-incl b)
  CoeqHom→ ϕ (coeq a i) = lem i
    where
    lem : incl (ϕ .hom-incl (f a)) ≡ incl (ϕ .hom-incl (g a))
    lem = cong incl {!!}

  CoeqEquiv : Type (ℓ-max ℓ ℓ')
  CoeqEquiv = Σ CoeqHom λ h → isEquiv (h .hom-incl) × isEquiv (h .hom-coeq)

  Coeq≃ : CoeqEquiv → Coeq f g ≃ Coeq f' g'
  Coeq≃ = {!!}
