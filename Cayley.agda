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

-- Coequalizer of two maps
data Coeq {A : Type ℓ} {B : Type ℓ'} (f g : A → B) : Type (ℓ-max ℓ ℓ') where
  incl : B → Coeq f g
  coeq : (a : A) → incl (f a) ≡ incl (g a)

-- Flattening for coequalizers
module FlatteningLemma {A : Type ℓ} {B : Type ℓ'} (f g : A → B) (P : B → Type ℓ'') (p : (a : A) → P (f a) ≡ P (g a)) where

  P' : Coeq f g → Type ℓ''
  P' (incl x)   = P x
  P' (coeq a i) = p a i

  ΣAP = Σ A (P ∘ f)

  Σf : ΣAP → Σ B P
  Σf (a , x) = f a , x

  Σg : ΣAP → Σ B P
  Σg (a , x) = g a , transport (p a) x

  postulate
    -- See the HoTT book, section 6.12
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

    eq : ⟨ X ⟩ → (embase ≡ embase) ≡ (embase ≡ embase)
    eq a = ua (compPathrEquiv (emloop (γ a)))

    open FlatteningLemma f g (λ _ → embase ≡ embase) eq

    G→EM : ⟨ G ⟩ → embase ≡ embase
    G→EM = transport⁻ (ΩEM₁≡ G)

    EM→G : embase ≡ embase → ⟨ G ⟩
    EM→G = transport (ΩEM₁≡ G)

    postulate
      EM→G-emloop : (u : ⟨ G ⟩) → EM→G (emloop u) ≡ u
      EM→G∙ : (p q : embase ≡ embase) → EM→G (p ∙ q) ≡ EM→G p · EM→G q

    Cayley≃Σ : Cayley ≃ Coeq Σf Σg
    Cayley≃Σ = isoToEquiv e
      where
      open Iso
      e : Iso Cayley (Coeq Σf Σg)
      fun e (vertex u) = incl (tt , G→EM u)
      fun e (edge u x i) = {!!}
      -- lem i
        where
        lem'' : PathP (λ j → embase ≡ transport⁻ (ΩEM₁≡ G) (γ x) j) (G→EM u) (G→EM u ∙ G→EM (γ x))
        lem'' = compPath-filler (transport⁻ (ΩEM₁≡ G) u) (G→EM (γ x))
        lem' : PathP (λ j → embase ≡ transport⁻ (ΩEM₁≡ G) (γ x) j) (transport⁻ (ΩEM₁≡ G) u) (transport⁻ (ΩEM₁≡ G) (u · γ x))
        lem' = {!!}
        -- lem : PathP (λ j → {!Coeq f g!}) (incl (tt , transport⁻ (ΩEM₁≡ G) u)) (incl (tt , transport⁻ (ΩEM₁≡ G) (u · γ x)))
        -- lem = {!!}
        -- lem'' : transport⁻ (ΩEM₁≡ G) u ≡ transport⁻ (ΩEM₁≡ G) u ∙ transport⁻ (ΩEM₁≡ G) (γ x)
        -- lem'' = {!!}
        -- lem' : transport⁻ (ΩEM₁≡ G) u ≡ transport⁻ (ΩEM₁≡ G) (u · γ x)
        -- lem' = {!!}
        -- lem : incl (tt , transport⁻ (ΩEM₁≡ G) u) ≡ incl (tt , transport⁻ (ΩEM₁≡ G) (u · γ x))
        -- lem = cong incl (ΣPathP (refl , lem'))
      inv e (incl (tt , p)) = vertex (EM→G p)
      inv e (coeq (x , p) i) = lem i
        where
        lem'' : vertex (EM→G p) ≡ vertex (EM→G p · γ x)
        lem'' = edge (EM→G p) x
        lem' : vertex (EM→G p) ≡ vertex (EM→G (p ∙ emloop (γ x)))
        lem' = lem'' ∙ cong (λ u → vertex (EM→G p · u)) (sym (EM→G-emloop (γ x))) ∙ cong vertex (sym (EM→G∙ p (emloop (γ x))))
        lem : vertex (EM→G p) ≡ vertex (EM→G (snd (g x , transport (eq x) p))) -- Σg (x , p)
        lem = {!!}
      -- cong vertex lem i
        -- where
        -- lem : EM→G p ≡ EM→G (transport (ua (compPathrEquiv (emloop (γ x)))) p) -- (p ∙ emloop (γ x))
        -- lem = {!!}
      rightInv e (incl (tt , x)) = cong incl (ΣPathP (refl , (transport⁻Transport (ΩEM₁≡ G) x)))
      rightInv e (coeq a i) = {!!}
      leftInv e (vertex x) = cong vertex (transportTransport⁻ (ΩEM₁≡ G) x)
      leftInv e (edge u x i) = {!!}

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
    equiv : (x : Coeq f g) → FlatteningLemma.P' f g (λ _ → embase ≡ embase) (λ a → ua (compPathrEquiv (emloop (γ a)))) x ≃ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) x))
    equiv (incl tt) = idEquiv _
    equiv (coeq x i) = {!!}



