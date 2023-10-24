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
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.FreeGroup as FG renaming (_·_ to _·f_)
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
U : {G : Group ℓ} {X : hSet ℓ} (ι : ⟨ X ⟩ → ⟨ G ⟩) → GSet G → XSet X
U {G = G} {X = X} ι (A , strA) = A , xsetstr (action ϕ∘ι  isSetA)
  where
  isSetA = strA .GSetStr.is-set
  ϕ = strA .GSetStr._*_
  ϕ∘ι : ⟨ X ⟩ → A → A
  ϕ∘ι x a = ϕ (ι x) a

-- -- the action of U F extends the one of F on generators
-- Ugen : {G : Group ℓ} {X : hSet ℓ} (ι : ⟨ X ⟩ → ⟨ G ⟩) (F : GSet G) (x : ⟨ X ⟩) (a : ⟨ F ⟩) → (XSetStr.ϕ (str (U {G = G} {X = X} ι F)) SetAction.* x) a ≡ (GSetStr.ϕ (str F) Action.* (ι x)) a
-- Ugen ι F x a = refl

XSetΣ : (X : hSet ℓ) → Type _
XSetΣ {ℓ = ℓ} X = Σ (Type ℓ) λ A → (⟨ X ⟩ → A → A) × isSet A

XSet≃Σ : {ℓ : Level} {X : hSet ℓ} → XSet X ≃ XSetΣ X
XSet≃Σ {ℓ = ℓ} {X = X} = isoToEquiv e
  where
  open Iso
  open XSetStr
  open SetAction
  e : Iso (XSet X) (Σ (Type ℓ) λ A → (⟨ X ⟩ → A → A) × isSet A)
  fun e S = ⟨ S ⟩ , str S .ϕ ._*_ , str S .ϕ .is-set
  Iso.inv e (A , f , SA) = A , (xsetstr (action f SA))
  rightInv e (A , f , SA) = refl
  leftInv e S = refl

XSet≡Σ : {X : hSet ℓ} (A B : XSet X) → Type _
XSet≡Σ {X = X} A B = (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a)))

XSet≡≃Σ : {X : hSet ℓ} {A B : XSet X} → (A ≡ B) ≃ XSet≡Σ A B
XSet≡≃Σ {X = X} {A = A} {B = B} =
  A ≡ B ≃⟨ cong (equivFun XSet≃Σ) , isEquiv→isEmbedding (snd XSet≃Σ) A B ⟩
  A' ≡ B' ≃⟨ invEquiv (ΣPathTransport≃PathΣ A' B') ⟩
  Σ (⟨ A ⟩ ≡ ⟨ B ⟩) (λ p → subst (λ A → (⟨ X ⟩ → A → A) × isSet A) p (snd A') ≡ snd B') ≃⟨ Σ-cong-equiv-snd (λ p → invEquiv (Σ≡PropEquiv λ _ → isPropIsSet)) ⟩
  Σ (⟨ A ⟩ ≡ ⟨ B ⟩) (λ p → subst (λ A → (⟨ X ⟩ → A → A)) p fA ≡ fB) ≃⟨ Σ-cong-equiv-snd (λ p → pathToEquiv (lem p)) ⟩
  (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a))) ■
  where
    open XSetStr
    open SetAction
    A' = equivFun XSet≃Σ A
    B' = equivFun XSet≃Σ B
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

GSet≡Σ : {G : Group ℓ} (A B : GSet G) → Type _
GSet≡Σ {G = G} A B = Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ G ⟩) (a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) x a) ≡ (str B .GSetStr._*_) x (transport p a))

postulate
  GSet≡≃Σ : {G : Group ℓ} {A B : GSet G} → (A ≡ B) ≃ GSet≡Σ A B

module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  open GroupStr (str G)
  open principal-torsor {G = G}
  open generators {G = G} {X = X} {ι = ι}
  module _ {generates : ι-generates} where

    isoΣ : Iso (GSet≡Σ PG PG) (XSet≡Σ {X = X} (U ι PG) (U ι PG))
    Iso.fun isoΣ (p , q) = p , λ x a → q (ι x) a
    Iso.inv isoΣ (p , q) = p , {!!}
      where
      open GSetStr
      open Action
      ι* = ι-star-hom .fst
      α = str PG .ϕ
      isSetG : isSet ⟨ G ⟩
      isSetG = α .is-set
      comm : (x : ⟨ G ⟩) (a : ⟨ PG ⟩) → transport p ((α * x) a) ≡ (α * x) (transport p a)
      comm x a = PT.rec (isSetG _ _) (λ { (u , r) → {!!} }) s
        where
        s : ∥ Σ (FreeGroup ⟨ X ⟩) (λ u → ι* u ≡ x) ∥₁
        s = generates x
        comm' : (u : FreeGroup ⟨ X ⟩) → ι* u ≡ x → transport p ((α * x) a) ≡ (α * x) (transport p a)
        comm' = FG.elimProp
          (λ _ → isPropΠ λ _ → isSetG _ _)
          (λ y r →
            transport p ((α * x) a) ≡⟨ {!!} ⟩ -- by r
            transport p ((α * ι* (η y)) a) ≡⟨ {!!} ⟩ -- ι* is an extension of ι
            transport p ((α * ι y) a) ≡⟨ refl ⟩ -- property of U
            transport p ((XSetStr.ϕ (str (U {X = X} ι PG)) SetAction.* y) a) ≡⟨ q y a ⟩
            (XSetStr.ϕ (str (U {X = X} ι PG)) SetAction.* y) (transport p a) ≡⟨ refl ⟩ -- property of U
            (α * (ι y)) (transport p a) ≡⟨ {!!} ⟩ -- by r
            (α * x) (transport p a) ∎)
          (λ u v r s t →
            transport p ((α * x) a) ≡⟨ {!!} ⟩ -- by t
            transport p ((α * ι* (u ·f v)) a) ≡⟨ {!!} ⟩ -- ι* morphism of groups
            transport p ((α * (ι* u · ι* v)) a) ≡⟨ {!!} ⟩ -- α action
            transport p ((α * (ι* u)) ((α * (ι* v)) a)) ≡⟨ {!!} ⟩
            {!transport p ((α * (ι* u)) ((α * (ι* v)) a))!} ≡⟨ {!!} ⟩
            (α * x) (transport p a) ∎)
          {!!}
          {!!}
    Iso.rightInv isoΣ = {!!}
    Iso.leftInv isoΣ = {!!}




-- postulate
  -- -- by XSet≡ above
  -- splitXSet≡ : {X : hSet ℓ} {A B : XSet X} → (A ≡ B) ≃ XSet≡Σ A B
  -- splitGSet≡ : {G : Group ℓ} {A B : GSet G} → (A ≡ B) ≃ GSet≡Σ A B

-- theorem1 : {G : Group ℓ} {A B : GSet G} {p : ⟨ A ⟩ ≡ ⟨ B ⟩} {g : ⟨ G ⟩} → isProp ((a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a))
-- theorem1 {B = B} = isPropΠ λ _ → str B .GSetStr.ϕ .Action.is-set _ _

-- theorem2 : {X : hSet ℓ} {A B : XSet X} {p : ⟨ A ⟩ ≡ ⟨ B ⟩} → isProp ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a))
-- theorem2 {B = B} = isPropΠ λ _ → isPropΠ λ _ → str B .XSetStr.ϕ .SetAction.is-set _ _

-- theorem3 : {G : Group ℓ} {A B : GSet G} {p : ⟨ A ⟩ ≡ ⟨ B ⟩} → isProp ((g : ⟨ G ⟩) (a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a))
-- theorem3 {B = B} = isPropΠ λ _ → isPropΠ λ _ → str B .GSetStr.ϕ .Action.is-set _ _

-- module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  -- open GroupStr (str G)
  -- open principal-torsor {G = G}
  -- open generators {G = G} {X = X} {ι = ι}
  -- module _ {generates : ι-generates} where
    -- thm : Iso (PG ≡ PG) (U ι PG ≡ U ι PG)
    -- Iso.fun thm eq = invEq (splitXSet≡ {X = X}) (p , λ x a → comm (ι x) a)
      -- where
      -- t = equivFun splitGSet≡ eq
      -- p = fst t
      -- comm = snd t
    -- Iso.inv thm eq = invEq splitGSet≡ (p , comm-star)
      -- where
      -- t = equivFun splitXSet≡ eq
      -- p : ⟨ G ⟩ ≡ ⟨ G ⟩
      -- p = fst t
      -- comm = snd t
      -- comm-star : (g : ⟨ G ⟩) → (a : ⟨ G ⟩) → (transport p (g · a)) ≡ (g · (transport p a))
      -- comm-star g = PT.rec (theorem1 {G = G} {A = PG} {B = PG} {p = p} {g = g}) lem (generates g)
        -- where
        -- lem : (Σ (FreeGroup ⟨ X ⟩) λ x → (ι-star-hom .fst x ≡ g)) → ((a : ⟨ G ⟩) → transport p (g · a) ≡ g · (transport p a))
        -- lem (x , prf) a =
          -- transport p (g · a)                       ≡⟨ cong (λ y → transport p (y · a)) (sym prf) ⟩
          -- transport p ((ι-star-hom .fst x)  · a)     ≡⟨ {!!} ⟩ -- gonna have to show that this function of 'x' is a morphism from FreeGroupGroup X to G and use uniqueness
          -- (ι-star-hom .fst x) · (transport p a)      ≡⟨ cong (λ y → y · (transport p a)) prf ⟩
          -- g · (transport p a) ∎
    -- Iso.rightInv thm eq = sym (
      -- eq ≡⟨ sym (retEq splitXSet≡ eq) ⟩
      -- (invEq splitXSet≡) (equivFun splitXSet≡ eq) ≡⟨ refl ⟩
      -- (invEq splitXSet≡) (p , com) ≡⟨ {!!} ⟩
      -- (Iso.fun thm) (Iso.inv thm eq) ∎)
        -- where
        -- t = equivFun splitXSet≡ eq
        -- p = fst t
        -- com = snd t
    -- -- Iso.rightInv thm eq = invEq (congEquiv splitXSet≡) (ΣPathP ( {!!} , (theorem2 _ _)))
    -- Iso.leftInv thm eq = {!!}
