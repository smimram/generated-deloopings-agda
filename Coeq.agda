{-# OPTIONS --cubical #-}

module Coeq where

open import Cubical.Foundations.Everything

private variable
  ℓ ℓ' ℓ'' : Level

module _ {A : Type ℓ} {B : Type ℓ'} (f g : A → B) where

  -- Coequalizer of two maps
  data Coeq : Type (ℓ-max ℓ ℓ') where
    incl : B → Coeq
    coeq : (a : A) → incl (f a) ≡ incl (g a)

  -- Elimination principle for coequalizers
  elim : (C : Coeq → Type ℓ'') (Ci : (b : B) → C (incl b)) (Ce : (a : A) → PathP (λ i → cong C (coeq a) i) (Ci (f a)) (Ci (g a))) (x : Coeq) → C x
  elim C Ci Ce (incl b) = Ci b
  elim C Ci Ce (coeq a i) = Ce a i
