{-

  This file contains:

  - The forgetful functor U from GSets to XSets when X is a subset of G
  - Proof that the the loop space of the principal torsor is invariant by U.

  -}

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.FreeGroup renaming (_·_ to _·f_)
open import Cubical.Data.Sigma

open import Base
open import XSet
open import GSet
open import GSetProperties
open import Generators
open import PrincipalTorsor

private
  variable
    ℓ ℓ' : Level

-- A natural forgetful functor for subsets of groups:
U : {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} → GSet G → XSet X
U {G = G} {X = X} {ι = ι} (A , strA) = A , xsetstr (action ϕ∘ι  isSetA)
  where
  isSetA = strA .GSetStr.is-set
  ϕ = strA .GSetStr._*_
  ϕ∘ι : ⟨ X ⟩ → A → A
  ϕ∘ι x a = ϕ (ι x) a

XSetΣ : {ℓ : Level} {X : hSet ℓ} → XSet X ≃ Σ (Type ℓ) λ A → (⟨ X ⟩ → A → A) × isSet A
XSetΣ {ℓ = ℓ} {X = X} = isoToEquiv e
  where
  open Iso
  open XSetStr
  open SetAction
  e : Iso (XSet X) (Σ (Type ℓ) λ A → (⟨ X ⟩ → A → A) × isSet A)
  fun e S = ⟨ S ⟩ , str S .ϕ ._*_ , str S .ϕ .is-set
  Iso.inv e (A , f , SA) = A , (xsetstr (action f SA))
  rightInv e (A , f , SA) = refl
  leftInv e S = refl

XSet≡ : {X : hSet ℓ} {A B : XSet X} → (A ≡ B) ≃ (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a)))
XSet≡ {X = X} {A = A} {B = B} =
  A ≡ B ≃⟨ cong (equivFun XSetΣ) , isEquiv→isEmbedding (snd XSetΣ) A B ⟩
  A' ≡ B' ≃⟨ invEquiv (ΣPathTransport≃PathΣ A' B') ⟩
  Σ (⟨ A ⟩ ≡ ⟨ B ⟩) (λ p → subst (λ A → (⟨ X ⟩ → A → A) × isSet A) p (snd A') ≡ snd B') ≃⟨ Σ-cong-equiv-snd (λ p → invEquiv (Σ≡PropEquiv λ _ → isPropIsSet)) ⟩
  Σ (⟨ A ⟩ ≡ ⟨ B ⟩) (λ p → subst (λ A → (⟨ X ⟩ → A → A)) p fA ≡ fB) ≃⟨ Σ-cong-equiv-snd (λ p → pathToEquiv (lem p)) ⟩
  (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a))) ■
  where
    open XSetStr
    open SetAction
    A' = equivFun XSetΣ A
    B' = equivFun XSetΣ B
    fA = str A .ϕ ._*_
    fB = str B .ϕ ._*_
    lem  = λ (p : ⟨ A ⟩ ≡ ⟨ B ⟩) →
      subst (λ A → ⟨ X ⟩ → A → A) p fA ≡ fB ≡⟨ refl ⟩
      transport (cong (λ A → ⟨ X ⟩ → A → A) p) fA ≡ fB ≡⟨ ua (compLEquiv (sym (fromPathP (funTypeTransp (λ _ → ⟨ X ⟩) (λ A → A → A) p fA)))) ⟩
      subst (λ A → A → A) p ∘ fA ∘ subst (λ _ → ⟨ X ⟩) (sym p) ≡ fB ≡⟨ refl ⟩
      subst (λ A → A → A) p ∘ fA ∘ transport refl ≡ fB ≡⟨ {!!} ⟩ -- transportRefl
      subst (λ A → A → A) p ∘ fA ≡ fB ≡⟨ ua (compLEquiv (sym (funExt λ x → sym (fromPathP (funTypeTransp (λ A → A) (λ A → A) p (fA x)))))) ⟩
      (λ x → subst (λ A → A) p ∘ fA x ∘ subst (λ A → A) (sym p)) ≡ fB ≡⟨ refl ⟩
      (λ x → transport p ∘ fA x ∘ transport (sym p)) ≡ fB ≡⟨ sym (ua funExt≃) ⟩
      ((x : ⟨ X ⟩) → transport p ∘ fA x ∘ transport (sym p) ≡ fB x) ≡⟨ ua (equivΠCod (λ x → invEquiv funExt≃)) ⟩
      ((x : ⟨ X ⟩) (b : ⟨ B ⟩) → transport p (fA x (transport (sym p) b)) ≡ fB x b) ≡⟨ {!!} ⟩ -- precomposition by transport p
      ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((ϕ (str A) * x) a) ≡ (ϕ (str B) * x) (transport p a)) ∎

postulate
  splitXSet≡ : {X : hSet ℓ} {A B : XSet X} → (A ≡ B) ≃ (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a)))
  splitGSet≡ : {G : Group ℓ} {A B : GSet G} → (A ≡ B) ≃ (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((g : ⟨ G ⟩) (a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a)))

  theorem1 : {G : Group ℓ} {A B : GSet G} {p : ⟨ A ⟩ ≡ ⟨ B ⟩} {g : ⟨ G ⟩} → isProp ((a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a))
  theorem2 : {X : hSet ℓ} {A B : XSet X} {p : ⟨ A ⟩ ≡ ⟨ B ⟩} → isProp ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a))
  theorem3 : {G : Group ℓ} {A B : GSet G} {p : ⟨ A ⟩ ≡ ⟨ B ⟩} → isProp ((g : ⟨ G ⟩) (a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a))

module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  open GroupStr (str G)
  open principal-torsor {G = G}
  open generators {G = G} {X = X} {ι = ι}
  module _ {generates : ι-generates} where
    thm : Iso (PG ≡ PG) (U PG ≡ U PG)
    Iso.fun thm eq = invEq (splitXSet≡ {X = X}) (p , λ x a → comm (ι x) a)
      where
      t = equivFun splitGSet≡ eq
      p = fst t
      comm = snd t
    Iso.inv thm eq = invEq splitGSet≡ (p , comm-star)
      where
      t = equivFun splitXSet≡ eq
      p : ⟨ G ⟩ ≡ ⟨ G ⟩
      p = fst t
      comm = snd t
      comm-star : (g : ⟨ G ⟩) → (a : ⟨ G ⟩) → (transport p (g · a)) ≡ (g · (transport p a))
      comm-star g = Cubical.HITs.PropositionalTruncation.rec (theorem1 {G = G} {A = PG} {B = PG} {p = p} {g = g}) lem (generates g)
        where
        lem : (Σ (FreeGroup ⟨ X ⟩) λ x → (ι-star-hom .fst x ≡ g)) → ((a : ⟨ G ⟩) → transport p (g · a) ≡ g · (transport p a))
        lem (x , prf) a =
          transport p (g · a)                       ≡⟨ cong (λ y → transport p (y · a)) (sym prf) ⟩
          transport p ((ι-star-hom .fst x)  · a)     ≡⟨ {!!} ⟩ -- gonna have to show that this function of 'x' is a morphism from FreeGroupGroup X to G and use uniqueness
          (ι-star-hom .fst x) · (transport p a)      ≡⟨ cong (λ y → y · (transport p a)) prf ⟩
          g · (transport p a) ∎
    Iso.rightInv thm eq = sym (
      eq ≡⟨ {!!} ⟩
      (invEq splitXSet≡) (equivFun splitXSet≡ eq) ≡⟨ {!!} ⟩
      (invEq splitXSet≡) (p , com) ≡⟨ {!!} ⟩
      (Iso.fun thm) (Iso.inv thm eq) ∎)
        where
        t = equivFun splitXSet≡ eq
        p = fst t
        com = snd t
    -- Iso.rightInv thm eq = invEq (congEquiv splitXSet≡) (ΣPathP ( {!!} , (theorem2 _ _)))
    Iso.leftInv thm eq = {!!}
