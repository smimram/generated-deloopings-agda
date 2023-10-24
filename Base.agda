{-# OPTIONS --cubical #-}

---
--- Lemmas which ought to be in the standard library...
---

open import Cubical.Foundations.Everything

private
  variable
    ℓ ℓ' : Level

-- should be somewhere in the standard library...
congComp : {A B : Type ℓ} {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ cong f p ∙ cong f q
congComp f p q = J (λ z q → cong f (p ∙ q) ≡ cong f p ∙ cong f q) (cong (cong f) (sym (rUnit p)) ∙ rUnit (cong f p)) q

-- funExt is an equivalence
funExt≃ : {A : Type ℓ} {B : A → I → Type ℓ'} {f : (x : A) → B x i0} {g : (x : A) → B x i1} →
          ((x : A) → PathP (B x) (f x) (g x)) ≃ PathP (λ i → (x : A) → B x i) f g
funExt≃ {A = A} {B = B} {f = f} {g = g} = isoToEquiv e
  where
  open Iso
  e : Iso ((x : A) → PathP (B x) (f x) (g x)) (PathP (λ i → (x : A) → B x i) f g)
  fun e p = funExt p
  inv e p = funExt⁻ p
  rightInv e p = refl
  leftInv  e p = refl

compLEquiv : {A : Type ℓ} {x y z : A} (p : x ≡ y) → (y ≡ z) ≃ (x ≡ z)
compLEquiv {x = x} {y = y} {z = z} p = isoToEquiv e
  where
  open Iso
  e : Iso (y ≡ z) (x ≡ z)
  fun e q = p ∙ q
  inv e q = sym p ∙ q
  rightInv e q = assoc _ _ _ ∙ cong (λ p → p ∙ q) (rCancel p) ∙ sym (lUnit q)
  leftInv e q = assoc _ _ _ ∙ cong (λ p → p ∙ q) (lCancel p) ∙ sym (lUnit q)
