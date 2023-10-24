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

XSet≡≃Σ : {X : hSet ℓ} (A B : XSet X) → (A ≡ B) ≃ XSet≡Σ A B
XSet≡≃Σ {X = X} A B =
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
  -- similar to XSet≡≃Σ
  GSet≡≃Σ : {G : Group ℓ} (A B : GSet G) → (A ≡ B) ≃ GSet≡Σ A B

module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  open GroupStr (str G)
  open principal-torsor {G = G}
  open generators {G = G} {X = X} {ι = ι}
  open IsGroupHom
  ι* = ι-star-hom .fst
  ι*GH = ι-star-hom .snd
  α = str PG .GSetStr.ϕ
  [α] = α .Action._*_
  isSetG : isSet ⟨ G ⟩
  isSetG = α .Action.is-set
  module _ {generates : ι-generates} where

    isoΣ : Iso (GSet≡Σ PG PG) (XSet≡Σ {X = X} (U ι PG) (U ι PG))
    Iso.fun isoΣ (p , q) = p , λ x a → q (ι x) a
    Iso.inv isoΣ (p , q) = p , λ x a → comm x a
      where
      open GSetStr
      open Action
      comm : (x : ⟨ G ⟩) (a : ⟨ PG ⟩) → transport p ([α] x a) ≡ [α] x (transport p a)
      comm x a = PT.rec (isSetG _ _) (λ { (u , r) → comm' u r }) s
        where
        s : ∥ Σ (FreeGroup ⟨ X ⟩) (λ u → ι* u ≡ x) ∥₁
        s = generates x
        comm* : (u : FreeGroup ⟨ X ⟩) → (a : ⟨ PG ⟩) → transport p ([α] (ι* u) a) ≡ [α] (ι* u) (transport p a)
        comm* = FG.elimProp
          (λ u → isPropΠ λ _ → isSetG _ _)
          (λ x a →
            transport p ([α] (ι* (η x)) a)                                   ≡⟨ refl ⟩ -- ι* is an extension of ι
            transport p ([α] (ι x) a)                                        ≡⟨ refl ⟩ -- property of U
            transport p (str (U {X = X} ι PG) .XSetStr.ϕ .SetAction._*_ x a) ≡⟨ q x a ⟩
            str (U {X = X} ι PG) .XSetStr.ϕ .SetAction._*_ x (transport p a) ≡⟨ refl ⟩ --property of U
            [α] (ι* (η x)) (transport p a)                                   ∎
          )
          (λ u v q r a →
            transport p ([α] (ι* (u ·f v)) a)       ≡⟨ cong (λ x → transport p ([α] x a)) (ι*GH .pres· u v) ⟩ -- morphism of groups
            transport p ([α] (ι* u · ι* v) a)       ≡⟨ cong (transport p) (sym (α .Action.·Composition _ _ a)) ⟩ -- α action
            transport p ([α] (ι* u) ([α] (ι* v) a)) ≡⟨ q _ ⟩
            [α] (ι* u) (transport p ([α] (ι* v) a)) ≡⟨ cong ([α] (ι* u)) (r _) ⟩
            [α] (ι* u) ([α] (ι* v) (transport p a)) ≡⟨ α .Action.·Composition _ _ _ ⟩ -- α action
            [α] (ι* u · ι* v) (transport p a)       ≡⟨ cong (λ x → [α] x (transport p a)) (sym (ι*GH .pres· u v)) ⟩ -- morphism of groups
            [α] (ι* (u ·f v)) (transport p a)       ∎
          )
          (λ a →
            transport p ([α] (ι* ε) a) ≡⟨ cong (λ x → transport p ([α] x a)) (ι*GH .pres1) ⟩ -- ι* morphism
            transport p ([α] 1g a)     ≡⟨ cong (transport p) (α .Action.·Unit a) ⟩ -- α action
            transport p a              ≡⟨ sym (α .Action.·Unit _) ⟩ -- α action
            [α] 1g (transport p a)     ≡⟨ cong (λ x → [α] x (transport p a)) (sym (ι*GH .pres1)) ⟩ -- ι* morphism
            [α] (ι* ε) (transport p a) ∎
          )
          (λ u q a →
            let inv = str G .GroupStr.inv in
            transport p ([α] (ι* (FG.inv u)) a) ≡⟨ cong (λ x → transport p ([α] x a)) (ι*GH .presinv u) ⟩ -- ι* morphism
            transport p ([α] (inv (ι* u)) a)    ≡⟨ sym (act-inv α (sym (sym (q _) ∙ cong (transport p) (α .Action.·Composition _ _ a) ∙ cong (transport p) (cong (λ x → [α] x a) (str G .GroupStr.·InvR _)) ∙ cong (transport p) (α .Action.·Unit a)))) ⟩
            [α] (inv (ι* u)) (transport p a)    ≡⟨ cong (λ x → [α] x (transport p a)) (ι*GH .presinv u) ⟩ -- ι* morphism
            [α] (ι* (FG.inv u)) (transport p a) ∎
          )
        comm' : (u : FreeGroup ⟨ X ⟩) → ι* u ≡ x → transport p ([α] x a) ≡ [α] x (transport p a)
        comm' u q = subst (λ x → transport p ([α] x a) ≡ [α] x (transport p a)) q (comm* u a)
    Iso.rightInv isoΣ (p , q) = Σ≡Prop (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetG _ _) refl
    Iso.leftInv isoΣ (p , q) = Σ≡Prop (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetG _ _) refl

    theorem : (PG ≡ PG) ≃ (U {X = X} ι PG ≡ U ι PG)
    theorem = compEquiv (GSet≡≃Σ PG PG) (compEquiv (isoToEquiv isoΣ) (invEquiv (XSet≡≃Σ (U ι PG) (U ι PG))))
