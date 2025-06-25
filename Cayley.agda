{-# OPTIONS --cubical #-}

---
--- Cayley graphs in homotopy type theory
---

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Algebra.Group
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.EilenbergMacLane1 as EM
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Generators
open import Coeq

private variable
  ℓ ℓ' ℓ'' : Level

-- Kernel of a map
ker : {A : Type ℓ} {B : Pointed ℓ'} (f : A → ⟨ B ⟩) → Type _
ker {A = A} {B = B} f = Σ A λ a → f a ≡ pt B

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

  -- The Cayley graph as a kernel
  Cayley-ker : Cayley ≃ Σ BX* (λ x → embase ≡ Bγ* x)
  Cayley-ker =
    Cayley                       ≃⟨ Cayley≃Coeq1 ⟩
    Coeq f1 g1                   ≃⟨ Coeq1≃Coeq ⟩
    Coeq Σf Σg                   ≃⟨ invEquiv flatten ⟩
    Σ (Coeq f g) P'              ≃⟨ Σ-cong-equiv (invEquiv (BX*≃Coeq)) (λ x → pathToEquiv (equiv x)) ⟩
    Σ BX* (λ x → embase ≡ Bγ* x) ■
    where
    f1 : ⟨ G ⟩ × ⟨ X ⟩ → ⟨ G ⟩
    f1 (g , x) = g

    g1 : ⟨ G ⟩ × ⟨ X ⟩ → ⟨ G ⟩
    g1 (g , x) = g · γ x

    -- Cayley as a coequalizer
    Cayley≃Coeq1 : Cayley ≃ Coeq f1 g1
    Cayley≃Coeq1 = isoToEquiv e
      where
      open Iso
      e : Iso Cayley (Coeq f1 g1)
      fun e (vertex u) = incl u
      fun e (edge u x i) = coeq (u , x) i
      inv e (incl u) = vertex u
      inv e (coeq (u , x) i) = edge u x i
      rightInv e (incl u) = refl
      rightInv e (coeq (u , x) i) = refl
      leftInv e (vertex u) = refl
      leftInv e (edge u x i) = refl

    f : ⟨ X ⟩ → Unit
    f _ = tt
    g = f

    eq : ⟨ X ⟩ → (embase ≡ embase) ≃ (embase ≡ embase)
    eq a = compPathrEquiv (emloop (γ a))

    -- Apply the flattening lemma
    open FlatteningLemma f g (λ _ → embase ≡ embase) eq

    -- Equivalence between the loop space of EM and G
    ΩEM≃G : (embase ≡ embase) ≃ ⟨ G ⟩
    ΩEM≃G = isoToEquiv (ΩEM₁Iso G)

    EM→G : embase ≡ embase → ⟨ G ⟩
    EM→G = equivFun ΩEM≃G

    G→EM : ⟨ G ⟩ → embase ≡ embase
    G→EM = invEq ΩEM≃G

    postulate
      -- The equivalence between the loop space of EM and G is actually a group
      -- isomorphism. This does classical fact does not seem to be proved in the
      -- standard library, admit it.
      G→EM∙ : (u v : ⟨ G ⟩) → G→EM u ∙ G→EM v ≡ G→EM (u · v)

    -- Compare the natural reformulation of Cayley as a coequalizer and the one
    -- we get from flattening.
    Coeq1≃Coeq : Coeq f1 g1 ≃ Coeq Σf Σg
    Coeq1≃Coeq = Coeq≃ f1 g1 Σf Σg (h , snd (isoToEquiv h0) , snd (isoToEquiv h1))
      where
      open Iso
      open CoeqHom

      h0 : Iso ⟨ G ⟩ (Unit × (embase ≡ embase))
      fun h0 u = tt , G→EM u
      inv h0 (tt , p) = EM→G p
      rightInv h0 (tt , p) = ΣPathP (refl , (retEq ΩEM≃G p))
      leftInv h0 u = secEq ΩEM≃G u

      h1 : Iso (⟨ G ⟩ × ⟨ X ⟩) (⟨ X ⟩ × (embase ≡ embase))
      fun h1 (u , x) = x , G→EM u
      inv h1 (x , p) = EM→G p , x
      rightInv h1 (x , p) = ΣPathP (refl , (retEq ΩEM≃G p))
      leftInv h1 (u , x) = ΣPathP (secEq ΩEM≃G u , refl)

      h : CoeqHom f1 g1 Σf Σg
      hom-incl h = fun h0
      hom-coeq h = fun h1
      hom-f h (u , x) = refl
      hom-g h (u , x) = ΣPathP (refl , lem)
        where
        lem =
          G→EM (g1 (u , x))        ≡⟨ refl ⟩
          G→EM (u · γ x)           ≡⟨ sym (G→EM∙ u (γ x)) ⟩
          G→EM u ∙ G→EM (γ x)      ≡⟨ refl ⟩
          G→EM u ∙ emloop (γ x)    ≡⟨ refl ⟩
          equivFun (eq x) (G→EM u) ≡⟨ refl ⟩
          equivFun (eq x) (G→EM u) ∎

    -- BX* as a coequalizer
    BX*≃Coeq : BX* ≃ Coeq f g
    BX*≃Coeq = isoToEquiv e
      where
      open Iso
      e : Iso BX* (Coeq f g)
      fun e base = incl tt
      fun e (loop x i) = coeq x i
      inv e (incl tt) = base
      inv e (coeq x i) = loop x i
      rightInv e (incl tt) = refl
      rightInv e (coeq x i) = refl
      leftInv e base = refl
      leftInv e (loop x i) = refl

    -- The formulation of substInPaths in previous versions of the standard
    -- library was not generic enough wrt universe levels.
    substInPaths' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a a' : A}
                 → (f g : A → B) → (p : a ≡ a') (q : f a ≡ g a)
                 → subst (λ x → f x ≡ g x) p q ≡ sym (cong f p) ∙ q ∙ cong g p
    substInPaths' {a = a} f g p q =
      J (λ x p' → (subst (λ y → f y ≡ g y) p' q) ≡ (sym (cong f p') ∙ q ∙ cong g p')) p=refl p
      where
      p=refl : subst (λ y → f y ≡ g y) refl q ≡ refl ∙ q ∙ refl
      p=refl =
        subst (λ y → f y ≡ g y) refl q ≡⟨ substRefl {B = (λ y → f y ≡ g y)} q ⟩
        q                              ≡⟨ (rUnit q) ∙ lUnit (q ∙ refl) ⟩
        refl ∙ q ∙ refl ∎

    -- Reformulating compPathrEquiv
    congCompPathrEquiv : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : y ≡ z) → ua (compPathrEquiv p) ≡ cong (λ y → x ≡ y) p
    congCompPathrEquiv {x = x} {y = y} = J (λ z p → ua (compPathrEquiv p) ≡ cong (λ y → x ≡ y) p) lem
      where
      lem' : compPathrEquiv refl ≡ idEquiv _
      lem' = equivEq (funExt λ p → sym (rUnit p))
      lem : ua (compPathrEquiv refl) ≡ refl
      lem = cong ua lem' ∙ uaIdEquiv

    -- Reformulation of P' through the equivalence BX*≃Coeq. Nothing very deep
    -- here.
    equiv : (x : Coeq f g) → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq x ≡ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) x))
    equiv = Coeq.elim f g
      (λ x → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq x ≡ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) x)))
      (λ tt → refl)
      (λ x → lem x)
      where
      lem' : (x : ⟨ X ⟩) → transport (cong (λ c → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq c ≡ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c))) (coeq x)) refl ≡ refl
      lem' x =
        transport (cong (λ c → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq c ≡ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c))) (coeq x)) refl ≡⟨ refl ⟩
        subst (λ c → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq c ≡ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c))) (coeq x) refl ≡⟨ substInPaths' (λ c → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq c) (λ c → embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c)) (coeq x) refl ⟩
        sym (cong (λ c → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq c) (coeq x)) ∙ refl ∙ cong (λ c → embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c)) (coeq x) ≡⟨ cong₂ _∙_ refl (sym (lUnit _)) ⟩
        sym (cong (λ c → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq c) (coeq x)) ∙ cong (λ c → embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c)) (coeq x) ≡⟨ refl ⟩
        sym (ua (eq x)) ∙ cong (λ c → embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c)) (coeq x)                  ≡⟨ refl ⟩
        sym (ua (eq x)) ∙ cong (λ m → embase ≡ m) (cong (λ c → Bγ* (equivFun (invEquiv BX*≃Coeq) c)) (coeq x)) ≡⟨ refl ⟩
        sym (ua (eq x)) ∙ cong (λ m → embase ≡ m) (cong Bγ* (cong (equivFun (invEquiv BX*≃Coeq)) (coeq x)))    ≡⟨ refl ⟩
        sym (ua (eq x)) ∙ cong (λ m → embase ≡ m) (cong Bγ* (loop x))                                          ≡⟨ refl ⟩
        sym (ua (compPathrEquiv (emloop (γ x)))) ∙ cong (λ m → embase ≡ m) (cong Bγ* (loop x))                 ≡⟨ cong₂ _∙_ (cong sym (congCompPathrEquiv _)) refl ⟩
        sym (cong (λ m → embase ≡ m) (emloop (γ x))) ∙ cong (λ m → embase ≡ m) (emloop (γ x))                  ≡⟨ lCancel _ ⟩
        refl                                                                                                   ∎
      lem : (x : ⟨ X ⟩) → PathP
        (λ i → cong (λ c → FlatteningLemma.P' f g (λ tt → embase ≡ embase) eq c ≡ (embase ≡ Bγ* (equivFun (invEquiv BX*≃Coeq) c))) (coeq x) i)
        refl
        refl
      lem x = toPathP (lem' x)

  open import Cubical.Algebra.Group.Morphisms
  open import Cubical.HITs.FreeGroup as FG renaming (_·_ to _·*_)

  -- Canonical extension of edge to the free group
  edge* : (g : ⟨ G ⟩) (u : FreeGroup ⟨ X ⟩) → vertex g ≡ vertex (g · freeGHom {X = X} {G = G} γ .fst u)
  edge* g (η x) = edge g x
  edge* g (u ·* v) = edge* g u ∙ edge* _ v ∙ cong vertex (sym (IsGroup.·Assoc isGroup _ (freeGHom {X = X} γ .fst u) (freeGHom {X = X} γ .fst v)) )
  edge* g ε = cong vertex (sym (IsGroup.·IdR (GroupStr.isGroup (G .snd)) g))
  edge* g (FG.inv u) = {!!}
  edge* g (FG.assoc u v w i) = {!!}
  edge* g (idr u i) = lem i
    where
    lem' : edge* g u ∙ (λ i → vertex (g · freeGHom {X = X} {G = G} γ .fst (idr u i))) ≡ refl ∙ edge* g u ∙ cong vertex (sym (IsGroup.·IdR (GroupStr.isGroup (G .snd)) (g · freeGHom {X = X} γ .fst u))) ∙ cong vertex (sym (IsGroup.·Assoc isGroup _ (freeGHom {X = X} γ .fst u) 1g))
    lem' = ?
    lem : Square
      (edge* g u)
      (edge* g u ∙ cong vertex (sym (IsGroup.·IdR (GroupStr.isGroup (G .snd)) (g · freeGHom {X = X} γ .fst u))) ∙ cong vertex (sym (IsGroup.·Assoc isGroup _ (freeGHom {X = X} γ .fst u) 1g)))
      (λ _ → vertex g)
      (λ i → vertex (g · freeGHom {X = X} {G = G} γ .fst (idr u i)))
    lem = {!!}
  edge* g (idl u i) = {!!}
  edge* g (invr u i) = {!!}
  edge* g (invl u i) = {!!}
  edge* g (trunc u v x y i j) = {!!}

  Cayley-connected : (x : Cayley) → ∥ vertex (GroupStr.1g (str G)) ≡ x ∥₁
  Cayley-connected = Cayley-elim
    (λ x → ∥ vertex (GroupStr.1g (str G)) ≡ x ∥₁)
    (λ g → PT.rec isPropPropTrunc (λ { (u , p) → ∣ edge* (GroupStr.1g (str G)) u ∙ cong vertex (·IdL _) ∙ cong vertex p ∣₁ }) (gen g))
    (λ _ _ → toPathP (isPropPropTrunc _ _))
