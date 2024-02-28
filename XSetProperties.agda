{-

  This file contains:

  - The forgetful functor U from GSets to XSets when X is a subset of G
  - Proof that the the loop space of the principal torsor is invariant by U.

  -}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.FreeGroup as FG renaming (_·_ to _·f_)
open import Cubical.Data.Sigma

open import XSet
open import GSet
open import GSetProperties
open import Generators
open import PrincipalTorsor

private variable
  ℓ ℓ' : Level

-- A natural forgetful functor for subsets of groups:
U : {X : hSet ℓ} {G : Group ℓ} (γ : ⟨ X ⟩ → ⟨ G ⟩) → GSet G → XSet X
U {X = X} {G = G} γ A = ⟨ A ⟩ , xsetstr (action ϕ∘γ  isSetA)
  where
  isSetA = (str A) .GSetStr.is-set
  ϕ = (str A) .GSetStr._*_
  ϕ∘γ : ⟨ X ⟩ → ⟨ A ⟩ → ⟨ A ⟩
  ϕ∘γ x a = ϕ (γ x) a

XSetΣ : (X : hSet ℓ) → Type _
XSetΣ {ℓ = ℓ} X = Σ (Type ℓ) λ A → (⟨ X ⟩ → A → A) × isSet A

-- Convert X-sets from records to Σ-types
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

-- Convert equalities of X-sets from records to Σ-types
XSet≡≃Σ : {X : hSet ℓ} (A B : XSet X) → (A ≡ B) ≃ XSet≡Σ A B
XSet≡≃Σ {X = X} A B =
  A ≡ B ≃⟨ cong (equivFun XSet≃Σ) , isEquiv→isEmbedding (snd XSet≃Σ) A B ⟩
  A' ≡ B' ≃⟨ invEquiv (ΣPathTransport≃PathΣ A' B') ⟩
  Σ (⟨ A ⟩ ≡ ⟨ B ⟩) (λ p → subst (λ A → (⟨ X ⟩ → A → A) × isSet A) p (snd A') ≡ snd B') ≃⟨ Σ-cong-equiv-snd (λ _ → invEquiv (Σ≡PropEquiv λ _ → isPropIsSet)) ⟩
  Σ (⟨ A ⟩ ≡ ⟨ B ⟩) (λ p → subst (λ A → (⟨ X ⟩ → A → A)) p fA ≡ fB)                     ≃⟨ Σ-cong-equiv-snd (λ p → pathToEquiv (lem p)) ⟩
  (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a))) ■
  where
    open XSetStr
    open SetAction
    A' = equivFun XSet≃Σ A
    B' = equivFun XSet≃Σ B
    fA = str A .ϕ ._*_
    fB = str B .ϕ ._*_
    lem  = λ (p : ⟨ A ⟩ ≡ ⟨ B ⟩) →
      subst (λ A → ⟨ X ⟩ → A → A) p fA ≡ fB                                         ≡⟨ refl ⟩
      transport (cong (λ A → ⟨ X ⟩ → A → A) p) fA ≡ fB                              ≡⟨ ua (compPathlEquiv (sym (fromPathP (funTypeTransp (λ _ → ⟨ X ⟩) (λ A → A → A) p fA)))) ⟩
      subst (λ A → A → A) p ∘ fA ∘ subst (λ _ → ⟨ X ⟩) (sym p) ≡ fB                 ≡⟨ refl ⟩
      subst (λ A → A → A) p ∘ fA ∘ transport refl ≡ fB                              ≡⟨ ua (compPathlEquiv {z = fB} (cong (λ x → subst (λ A → A → A) p ∘ x) (funExt {f = fA} {g = fA ∘ transport refl} λ x → cong fA (sym (transportRefl x))))) ⟩ -- transportRefl
      subst (λ A → A → A) p ∘ fA ≡ fB                                               ≡⟨ ua (compPathlEquiv (sym (funExt λ x → sym (fromPathP (funTypeTransp (λ A → A) (λ A → A) p (fA x)))))) ⟩
      (λ x → subst (λ A → A) p ∘ fA x ∘ subst (λ A → A) (sym p)) ≡ fB               ≡⟨ refl ⟩
      (λ x → transport p ∘ fA x ∘ transport (sym p)) ≡ fB                           ≡⟨ sym (ua funExtEquiv) ⟩
      ((x : ⟨ X ⟩) → transport p ∘ fA x ∘ transport (sym p) ≡ fB x)                 ≡⟨ ua (equivΠCod (λ x → invEquiv funExtEquiv)) ⟩
      ((x : ⟨ X ⟩) (b : ⟨ B ⟩) → transport p (fA x (transport (sym p) b)) ≡ fB x b) ≡⟨ ua (equivΠCod λ x → equivΠ (pathToEquiv (sym p)) λ b → invEquiv (compPathrEquiv (cong (fB x) (transportTransport⁻ p b))) ) ⟩ -- precomposition by transport p
      ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((ϕ (str A) * x) a) ≡ (ϕ (str B) * x) (transport p a)) ∎

GSet≡Σ : {G : Group ℓ} (A B : GSet G) → Type _
GSet≡Σ {G = G} A B = Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ G ⟩) (a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) x a) ≡ (str B .GSetStr._*_) x (transport p a))

postulate
  -- similar to XSet≡≃Σ
  GSet≡≃Σ : {G : Group ℓ} (A B : GSet G) → (A ≡ B) ≃ GSet≡Σ A B

module _ (G : Group ℓ) (X : hSet ℓ) (γ : ⟨ X ⟩ → ⟨ G ⟩) (gen : generates {X = X} {G = G} γ) where
  open GroupStr (str G)
  open IsGroupHom
  γ* = freeGHom {X = X} {G = G} γ .fst
  γ*GH = freeGHom {X = X} {G = G} γ .snd
  P = Principal
  α = str (P G) .GSetStr.ϕ
  [α] = α .Action._*_
  isSetG : isSet ⟨ G ⟩
  isSetG = α .Action.is-set

  -- One of our main results: the loop space of PG is the same as the loop space of PX
  theorem : (P G ≡ P G) ≃ (U {X = X} {G = G} γ (P G) ≡ U γ (P G))
  theorem = compEquiv (GSet≡≃Σ PG PG) (compEquiv (isoToEquiv isoΣ) (invEquiv (XSet≡≃Σ (U γ PG) (U γ PG))))
    where
    PG = Principal G
    isoΣ : Iso (GSet≡Σ PG PG) (XSet≡Σ {X = X} (U γ PG) (U γ PG))
    Iso.fun isoΣ (p , q) = p , λ x a → q (γ x) a
    Iso.inv isoΣ (p , q) = p , λ x a → comm x a
      where
      open GSetStr
      open Action
      comm : (x : ⟨ G ⟩) (a : ⟨ PG ⟩) → transport p ([α] x a) ≡ [α] x (transport p a)
      comm x a = PT.rec (isSetG _ _) (λ { (u , r) → comm' u r }) s
        where
        s : ∥ Σ (FreeGroup ⟨ X ⟩) (λ u → γ* u ≡ x) ∥₁
        s = gen x
        comm* : (u : FreeGroup ⟨ X ⟩) → (a : ⟨ PG ⟩) → transport p ([α] (γ* u) a) ≡ [α] (γ* u) (transport p a)
        comm* = FG.elimProp
          (λ u → isPropΠ λ _ → isSetG _ _)
          (λ x a →
            transport p ([α] (γ* (η x)) a)                                   ≡⟨ refl ⟩ -- γ* is an extension of γ
            transport p ([α] (γ x) a)                                        ≡⟨ refl ⟩ -- property of U
            transport p (str (U {X = X} γ PG) .XSetStr.ϕ .SetAction._*_ x a) ≡⟨ q x a ⟩
            str (U {X = X} γ PG) .XSetStr.ϕ .SetAction._*_ x (transport p a) ≡⟨ refl ⟩ --property of U
            [α] (γ* (η x)) (transport p a)                                   ∎
          )
          (λ u v q r a →
            transport p ([α] (γ* (u ·f v)) a)       ≡⟨ cong (λ x → transport p ([α] x a)) (γ*GH .pres· u v) ⟩ -- morphism of groups
            transport p ([α] (γ* u · γ* v) a)       ≡⟨ cong (transport p) (sym (α .Action.·Composition _ _ a)) ⟩ -- α action
            transport p ([α] (γ* u) ([α] (γ* v) a)) ≡⟨ q _ ⟩
            [α] (γ* u) (transport p ([α] (γ* v) a)) ≡⟨ cong ([α] (γ* u)) (r _) ⟩
            [α] (γ* u) ([α] (γ* v) (transport p a)) ≡⟨ α .Action.·Composition _ _ _ ⟩ -- α action
            [α] (γ* u · γ* v) (transport p a)       ≡⟨ cong (λ x → [α] x (transport p a)) (sym (γ*GH .pres· u v)) ⟩ -- morphism of groups
            [α] (γ* (u ·f v)) (transport p a)       ∎
          )
          (λ a →
            transport p ([α] (γ* ε) a) ≡⟨ cong (λ x → transport p ([α] x a)) (γ*GH .pres1) ⟩ -- γ* morphism
            transport p ([α] 1g a)     ≡⟨ cong (transport p) (α .Action.·Unit a) ⟩ -- α action
            transport p a              ≡⟨ sym (α .Action.·Unit _) ⟩ -- α action
            [α] 1g (transport p a)     ≡⟨ cong (λ x → [α] x (transport p a)) (sym (γ*GH .pres1)) ⟩ -- γ* morphism
            [α] (γ* ε) (transport p a) ∎
          )
          (λ u q a →
            let inv = str G .GroupStr.inv in
            transport p ([α] (γ* (FG.inv u)) a) ≡⟨ cong (λ x → transport p ([α] x a)) (γ*GH .presinv u) ⟩ -- γ* morphism
            transport p ([α] (inv (γ* u)) a)    ≡⟨ sym (act-inv α (sym (sym (q _) ∙ cong (transport p) (α .Action.·Composition _ _ a ∙ cong (λ x → [α] x a) (str G .GroupStr.·InvR _) ∙ α .Action.·Unit a)))) ⟩
            [α] (inv (γ* u)) (transport p a)    ≡⟨ cong (λ x → [α] x (transport p a)) (γ*GH .presinv u) ⟩ -- γ* morphism
            [α] (γ* (FG.inv u)) (transport p a) ∎
          )
        comm' : (u : FreeGroup ⟨ X ⟩) → γ* u ≡ x → transport p ([α] x a) ≡ [α] x (transport p a)
        comm' u q = subst (λ x → transport p ([α] x a) ≡ [α] x (transport p a)) q (comm* u a)
    Iso.rightInv isoΣ (p , q) = Σ≡Prop (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetG _ _) refl
    Iso.leftInv isoΣ (p , q) = Σ≡Prop (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSetG _ _) refl
