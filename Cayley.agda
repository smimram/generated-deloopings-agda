{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.EilenbergMacLane1 as EM
open import Cubical.HITs.Pushout
open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Generators

private variable
  ℓ ℓ' ℓ'' : Level

-- Kernel of a map
ker : {A : Type ℓ} {B : Pointed ℓ'} (f : A → ⟨ B ⟩) → Type _
ker {A = A} {B = B} f = Σ A λ a → f a ≡ pt B

module _ {A : Type ℓ} {B : Type ℓ'} (f g : A → B) where

  -- Coequalizer of two maps
  data Coeq : Type (ℓ-max ℓ ℓ') where
    incl : B → Coeq
    coeq : (a : A) → incl (f a) ≡ incl (g a)

  -- Elimination principle for coequalizers
  Coeq-elim : (C : Coeq → Type ℓ'') (Ci : (b : B) → C (incl b)) (Ce : (a : A) → PathP (λ i → cong C (coeq a) i) (Ci (f a)) (Ci (g a))) (x : Coeq) → C x
  Coeq-elim C Ci Ce (incl b) = Ci b
  Coeq-elim C Ci Ce (coeq a i) = Ce a i

-- Flattening for coequalizers
module FlatteningLemma {A : Type ℓ} {B : Type ℓ'} (f g : A → B) (P : B → Type ℓ'') (p : (a : A) → P (f a) ≃ P (g a)) where

  P' : Coeq f g → Type ℓ''
  P' (incl x)   = P x
  P' (coeq a i) = ua (p a) i

  ΣAP = Σ A (P ∘ f)

  Σf : ΣAP → Σ B P
  Σf (a , x) = f a , x

  Σg : ΣAP → Σ B P
  Σg (a , x) = g a , equivFun (p a) x

  postulate
    -- See the HoTT book, section 6.12. The cubical library unfortunately only
    -- contains a proof of the flattening lemma for pushouts (which is similar).
    flatten : Σ (Coeq f g) P' ≃ Coeq Σf Σg

module _ {G : Group ℓ} {X : hSet ℓ} (γ : ⟨ X ⟩ → ⟨ G ⟩) (gen : generates {X = X} {G = G} γ) where
  open GroupStr (str G)

  -- Delooping of the free group on the generators
  data BX* : Set ℓ where
    base : BX*
    loop : ⟨ X ⟩ → base ≡ base

  -- Canonical morphism from obtained by delooping γ*
  Bγ* : BX* → EM₁ G
  Bγ* base       = embase
  Bγ* (loop x i) = emloop (γ x) i

  -- The Cayley graph as a HIT
  -- This is also the coequalizer of X × G → G of (x,g) ↦ g and (x,g) ↦ g · γ x
  data Cayley : Type ℓ where
    vertex : ⟨ G ⟩ → Cayley
    edge   : (g : ⟨ G ⟩) (x : ⟨ X ⟩) → vertex g ≡ vertex (g · γ x)

  -- Elimination principle for the Cayley graph
  Cayley-elim : (A : Cayley → Type ℓ')
                (Av : (u : ⟨ G ⟩) → A (vertex u)) →
                ((u : ⟨ G ⟩) (x : ⟨ X ⟩) → PathP (λ i → cong A (edge u x) i) (Av u) (Av (u · γ x))) →
                (x : Cayley) → A x
  Cayley-elim A Av Ae (vertex x) = Av x
  Cayley-elim A Av Ae (edge g x i) = Ae g x i

  module _ where
    ff : ⟨ G ⟩ × ⟨ X ⟩ → ⟨ G ⟩
    ff (g , x) = ?

  -- The Cayley graph as a kernel
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

    -- Σf : Σ X (P ∘ f) → Σ 1 P

    eq : ⟨ X ⟩ → (embase ≡ embase) ≃ (embase ≡ embase)
    eq a = compPathrEquiv (emloop (γ a))

    open FlatteningLemma f g (λ _ → embase ≡ embase) eq

    ΩEM≃G : (embase ≡ embase) ≃ ⟨ G ⟩
    ΩEM≃G = isoToEquiv (ΩEM₁Iso G)

    EM→G : embase ≡ embase → ⟨ G ⟩
    EM→G = equivFun ΩEM≃G

    G→EM : ⟨ G ⟩ → embase ≡ embase
    G→EM = invEq ΩEM≃G

    postulate
      EM→G-emloop : (u : ⟨ G ⟩) → EM→G (emloop u) ≡ u
      EM→G∙ : (p q : embase ≡ embase) → EM→G (p ∙ q) ≡ EM→G p · EM→G q
      G→EM∙ : (u v : ⟨ G ⟩) → G→EM u ∙ G→EM v ≡ G→EM (u · v)

    Cayley≃Σ : Cayley ≃ Coeq Σf Σg
    Cayley≃Σ = isoToEquiv e
      where
      open Iso
      ϕ-vertex : (u : ⟨ G ⟩) → Coeq Σf Σg
      ϕ-vertex u = incl (tt , G→EM u)
      ϕ-edge : (u : ⟨ G ⟩) (x : ⟨ X ⟩) → incl (tt , G→EM u) ≡ incl (tt , G→EM (u · γ x))
      ϕ-edge u x =
        incl (tt , G→EM u)                   ≡⟨ coeq (x , (G→EM u)) ⟩
        incl (tt , equivFun (eq x) (G→EM u)) ≡⟨ cong (λ x → incl (tt , x)) (G→EM∙ u (γ x)) ⟩
        incl (tt , G→EM (u · γ x))           ∎

      ϕ : Cayley → Coeq Σf Σg
      ϕ (vertex u) = ϕ-vertex u
      ϕ (edge u x i) = ϕ-edge u x i
      ψ-incl : (p : embase ≡ embase) → Cayley
      ψ-incl p = vertex (EM→G p)
      ψ-coeq : (x : ⟨ X ⟩) (p : embase ≡ embase) → vertex (EM→G p) ≡ vertex (EM→G (p ∙ emloop (γ x)))
      ψ-coeq x p =
        vertex (EM→G p)                       ≡⟨ edge (EM→G p) x ⟩
        vertex (EM→G p · γ x)                 ≡⟨ cong (λ u → vertex (EM→G p · u)) (sym (EM→G-emloop (γ x))) ⟩
        vertex (EM→G p · EM→G (emloop (γ x))) ≡⟨ cong vertex (sym (EM→G∙ p (emloop (γ x)))) ⟩
        vertex (EM→G (p ∙ emloop (γ x)))      ∎
      ψ : Coeq Σf Σg → Cayley
      ψ (incl (tt , p)) = ψ-incl p
      ψ (coeq (x , p) i) = ψ-coeq x p i
      e : Iso Cayley (Coeq Σf Σg)
      fun e = ϕ
      inv e = ψ
      -- rightInv e (incl (tt , x)) = cong incl (ΣPathP (refl , retEq ΩEM≃G x))
      -- rightInv e (coeq a i) = {!!}
      rightInv e = Coeq-elim Σf Σg (λ x → ϕ (ψ x) ≡ x)
        ri-incl
        {!!} -- ri-coeq
        where
        ri-incl : (p : Unit × (embase ≡ embase)) → ϕ-vertex (EM→G (snd p)) ≡ incl p
        ri-incl (tt , p) = cong incl (ΣPathP (refl , retEq ΩEM≃G p))
        ri-coeq : (x : FlatteningLemma.ΣAP f g (λ _ → embase ≡ embase) eq) → PathP (λ i → cong (λ x → ϕ (ψ x) ≡ x) (coeq x) i) (ri-incl (FlatteningLemma.Σf f g (λ _ → embase ≡ embase) eq x)) (ri-incl (FlatteningLemma.Σg f g (λ _ → embase ≡ embase) eq x))
        ri-coeq (x , p) = lem
          where
          lem' : PathP (λ i → cong (λ x → ϕ (ψ x) ≡ x) (coeq (x , p)) i) (cong incl (ΣPathP (refl , retEq ΩEM≃G p))) (cong incl (ΣPathP (refl , (retEq ΩEM≃G (p ∙ emloop (γ x))))))
          lem' = {!!}
          lem : PathP (λ i → cong (λ x → ϕ (ψ x) ≡ x) (coeq (x , p)) i) (ri-incl (f x , p)) (ri-incl (g x , p ∙ emloop (γ x)))
          lem = {!!}
      leftInv e = Cayley-elim (λ x → ψ (ϕ x) ≡ x)
        li-vertex
        li-edge
        where
        li-vertex : (u : ⟨ G ⟩) → vertex (EM→G (G→EM u)) ≡ vertex u
        li-vertex u = cong vertex (secEq ΩEM≃G u)
        li-edge : (u : ⟨ G ⟩) (x : ⟨ X ⟩) →
                  PathP (λ i → cong (λ x → ψ (ϕ x) ≡ x) (edge u x) i) (li-vertex u) (li-vertex (u · γ x))
        li-edge u x = toPathP {!!} -- lem up to transporting over equality
          where
          lem : sym (cong (ψ ∘ ϕ) (edge u x)) ∙ li-vertex u ∙ edge u x ≡ li-vertex (u · γ x)
          lem =
            sym (cong (ψ ∘ ϕ) (edge u x)) ∙ li-vertex u ∙ edge u x ≡⟨ {!!} ⟩
            li-vertex (u · γ x) ∎

-- cong vertex (secEq ΩEM≃G u) ≡ {!cong vertex (secEq ΩEM≃G (u · γ x))!}

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
    equiv : (x : Coeq f g) → FlatteningLemma.P' f g (λ _ → embase ≡ embase) eq x ≃ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) x))
    equiv (incl tt) = idEquiv _
    equiv (coeq x i) = {!!}
