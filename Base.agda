{-# OPTIONS --cubical #-}

---
--- Lemmas which ought to be in the standard library...
---

open import Cubical.Foundations.Everything

private
  variable
    ℓ : Level

-- should be somewhere in the standard library...
congComp : {A B : Type ℓ} {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ cong f p ∙ cong f q
congComp f p q = J (λ z q → cong f (p ∙ q) ≡ cong f p ∙ cong f q) (cong (cong f) (sym (rUnit p)) ∙ rUnit (cong f p)) q

compLEquiv : {A : Type ℓ} {x y z : A} (p : x ≡ y) → (y ≡ z) ≃ (x ≡ z)
compLEquiv {x = x} {y = y} {z = z} p = isoToEquiv e
  where
  e : Iso (y ≡ z) (x ≡ z)
  e = {!!}
