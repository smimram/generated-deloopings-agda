{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything hiding (⋆)
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Data.Sigma
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Relation.Binary
open import Cubical.HITs.SetQuotients as SQ

private variable
  ℓ ℓ' : Level

subst2≡ : {A : Type ℓ} {x x' y y' : A} (p : x ≡ x') (q : y ≡ y') (r : x ≡ y) → subst2 _≡_ p q r ≡ sym p ∙ r ∙ q
subst2≡ p q r = {!!}

subst2≡Refl : {A : Type ℓ} {x y z : A} (p : y ≡ x) (q : y ≡ z) → subst2 _≡_ p q refl ≡ sym p ∙ q
subst2≡Refl p q =
  subst2 _≡_ p q refl ≡⟨ subst2≡ p q refl ⟩
  sym p ∙ refl ∙ q    ≡⟨ cong₂ _∙_ refl (sym (lUnit q)) ⟩
  sym p ∙ q           ∎

-- A span between two types
record Span (X Y : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    total : Type ℓ'
    src   : total → X
    tgt   : total → Y

open Span public

-- A graph is a span endomorphism
Graph : (X : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Graph {ℓ' = ℓ'} X = Span {ℓ' = ℓ'} X X

module _ (G : Group ℓ) where
  open GroupStr (str G)

  -- A relation is a congruence
  record isCongruence (_∼_ : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ) : Type ℓ where
    field
      equivalence : BinaryRelation.isEquivRel _∼_
      preservesProd : {x x' y y' : ⟨ G ⟩} → x ∼ x' → y ∼ y' → (x · y) ∼ (x' · y')
      -- preservesInverse : {x y : ⟨ G ⟩} → x ∼ y → inv x ∼ inv y

  open isCongruence public

  -- A congruence on a group
  Congruence : Type _
  Congruence = Σ (⟨ G ⟩ → ⟨ G ⟩ → Type ℓ) isCongruence

  isReflexive : (R : Congruence) {x : ⟨ G ⟩} → fst R x x
  isReflexive R {x} = snd R .equivalence .BinaryRelation.isEquivRel.reflexive x

  isTransitive : (R : Congruence) {x y z : ⟨ G ⟩} → fst R x y → fst R y z → fst R x z
  isTransitive R p q = snd R .equivalence .BinaryRelation.isEquivRel.transitive _ _ _ p q

  isSymmetric : (R : Congruence) {x y : ⟨ G ⟩} → fst R x y → fst R y x
  isSymmetric R p = snd R .equivalence .BinaryRelation.isEquivRel.symmetric _ _ p

  preservesProduct : (R : Congruence) {x x' y y' : ⟨ G ⟩} → fst R x x' → fst R y y' → fst R (x · y) (x' · y')
  preservesProduct R = snd R .preservesProd

  preserves≡ : (R : Congruence) → {x y : ⟨ G ⟩} → x ≡ y → fst R x y
  preserves≡ R {x = x} p = subst (fst R x) p (isReflexive R)

  -- Congruences preserve inverses
  preservesInverse : (R : Congruence) → {x y : ⟨ G ⟩} → fst R x y → fst R (inv x) (inv y)
  preservesInverse R {x} {y} p =
    -- x' ~ 1 x' ~ y' y x' ~ y' x x' ~ y' 1 ~ y'
    preserves≡ R (sym (·IdL (inv x))) ··
    preserves≡ R (cong (λ y → y · inv x) (sym (·InvL y))) ··
    preserves≡ R (sym (·Assoc _ _ _)) ··
    preservesProduct R (isReflexive R) (preservesProduct R (isSymmetric R p) (isReflexive R)) ··
    preservesProduct R (isReflexive R) (preserves≡ R (·InvR x)) ··
    preserves≡ R (·IdR (inv y))
    where
    infixr 30 _··_
    _··_ = isTransitive R

  module _ (R : Graph {ℓ' = ℓ} ⟨ G ⟩) where

    -- The free (or generated) congruence on a graph
    data freeCongruence : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ where
      fcBase : (r : total R) → freeCongruence (src R r) (tgt R r)
      -- fcCong : isCongruence freeCongruence
      fcRefl : {x : ⟨ G ⟩} → freeCongruence x x
      fcTrans : {x y z : ⟨ G ⟩} → freeCongruence x y → freeCongruence y z → freeCongruence x z
      fcSym : {x y : ⟨ G ⟩} → freeCongruence x y → freeCongruence y x
      fcProd : {x x' y y' : ⟨ G ⟩} → freeCongruence x x' → freeCongruence y y' → freeCongruence (x · y) (x' · y')

    -- The free congurence is a congurence
    freeCongruenceIsCongruence : isCongruence freeCongruence
    BinaryRelation.isEquivRel.reflexive (equivalence freeCongruenceIsCongruence) _ = fcRefl
    BinaryRelation.isEquivRel.symmetric (equivalence freeCongruenceIsCongruence) _ _ = fcSym
    BinaryRelation.isEquivRel.transitive (equivalence freeCongruenceIsCongruence) _ _ _ = fcTrans
    preservesProd freeCongruenceIsCongruence = fcProd

    -- The free congurence as a congurence
    freeCongruenceCongruence : Congruence
    freeCongruenceCongruence = freeCongruence , freeCongruenceIsCongruence

  -- Quotient of a group by a congruence
  quotient : Congruence → Group ℓ
  quotient R = (⟨ G ⟩ / fst R) , grp
    where
    open isCongruence (snd R)
    grp : GroupStr (⟨ G ⟩ / fst R)
    GroupStr.1g grp = [ 1g ]
    GroupStr._·_ grp x y = rec2 squash/ (λ x y → [ x · y ]) (λ _ _ _ r → eq/ _ _ (preservesProduct R r (isReflexive R))) (λ _ _ _ r → eq/ _ _ (preservesProduct R (isReflexive R) r)) x y
    GroupStr.inv grp x = SQ.rec squash/ (λ x → [ inv x ]) (λ _ _ r → eq/ _ _ (preservesInverse R r)) x
    IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup grp))) = squash/
    IsSemigroup.·Assoc (IsMonoid.isSemigroup (IsGroup.isMonoid (GroupStr.isGroup grp))) = SQ.elimProp3 (λ _ _ _ → squash/ _ _) λ x y z → cong [_] (·Assoc x y z)
    IsMonoid.·IdR (IsGroup.isMonoid (GroupStr.isGroup grp)) = SQ.elimProp (λ _ → squash/ _ _) λ x → cong [_] (·IdR x)
    IsMonoid.·IdL (IsGroup.isMonoid (GroupStr.isGroup grp)) = SQ.elimProp (λ _ → squash/ _ _) λ x → cong [_] (·IdL x)
    IsGroup.·InvR (GroupStr.isGroup grp) = SQ.elimProp (λ _ → squash/ _ _) λ x → cong [_] (·InvR x)
    IsGroup.·InvL (GroupStr.isGroup grp) = SQ.elimProp (λ _ → squash/ _ _) λ x → cong [_] (·InvL x)

open import Cubical.HITs.FreeGroup as FG hiding (assoc)

-- A group presentation
Presentation : {ℓ : Level} → Type _
Presentation {ℓ} = TypeWithStr ℓ (λ X → Graph {ℓ' = ℓ} (FreeGroup X))

_* : Presentation → Group ℓ
P * = freeGroupGroup ⟨ P ⟩

-- Group presented by a group presentation
∣_∣ : {ℓ : Level} → Presentation {ℓ} → Group ℓ
∣ P ∣ = quotient (P *) (freeCongruenceCongruence (P *) (str P))

module _ {ℓ : Level} (P : Presentation {ℓ}) where

  -- 1-skeleton of the delooping of a presentation
  data 1Delooping : Type ℓ where
    ⋆ : 1Delooping
    gen : (a : ⟨ P ⟩) → ⋆ ≡ ⋆

  -- From now on, we have to suppose that we have _set_ of relations
  module _ (SP : isSet ⟨ P ⟩) where

    postulate
      -- The 1-delooping is a groupoid when we have a set of generators. This is
      -- non-trivial and proved in Wärn's _Path spaces of pushouts_.
      isGroupoid1Delooping : isGroupoid 1Delooping

    -- Path associated to a formal composite
    path : (u : ⟨ P * ⟩) → ⋆ ≡ ⋆
    path (η a) = gen a
    path (u · v) = path u ∙ path v
    path ε = refl
    path (inv u) = sym (path u)
    path (FG.assoc u v w i) = assoc (path u) (path v) (path w) i
    path (idr u i) = rUnit (path u) i
    path (idl u i) = lUnit (path u) i
    path (invr u i) = rCancel (path u) i
    path (invl u i) = lCancel (path u) i
    path (trunc u v p q i j) = isGroupoid1Delooping ⋆ ⋆ (path u) (path v) (cong path p) (cong path q) i j

    -- The delooping of a presentation
    data Delooping : Type ℓ where
      inj : 1Delooping → Delooping
      rel : (r : total (str P)) → cong inj (path (src (str P) r)) ≡ cong inj (path (tgt (str P) r))
      gpd : isGroupoid Delooping

    open import Cubical.HITs.EilenbergMacLane1 as EM

    -- Our main theorem
    -- The termination checker does not manage to check termination in pathToEM
    -- {-# TERMINATING #-}
    theorem :
      (sec : fst ∣ P ∣ → ⟨ P * ⟩) →
      ((x : fst ∣ P ∣) → [ sec x ] ≡ x) →
      Delooping ≃ EM₁ ∣ P ∣
    theorem sec isSec = isoToEquiv e
      where

      f1 : 1Delooping → EM₁ ∣ P ∣
      f1 ⋆ = embase
      f1 (gen a i) = emloop [ η a ] i

      -- pathToEM : (u : ⟨ P * ⟩) → cong f1 (path u) ≡ emloop [ u ]
      -- pathToEM (η a) = refl
      -- pathToEM (u · v) =
        -- cong f1 (path u ∙ path v)                     ≡⟨ cong-∙ f1 (path u) (path v) ⟩
        -- cong f1 (path u) ∙ cong f1 (path v)           ≡⟨ cong₂ _∙_ (pathToEM u) (pathToEM v) ⟩
        -- emloop [ u ] ∙ emloop [ v ]                   ≡⟨ sym (emloop-comp ∣ P ∣ [ u ] [ v ]) ⟩
        -- emloop (GroupStr._·_ (snd ∣ P ∣) [ u ] [ v ]) ≡⟨ refl ⟩
        -- emloop [ u · v ]                              ∎
      -- pathToEM ε = sym (emloop-1g ∣ P ∣)
      -- pathToEM (inv u) =
        -- cong f1 (sym (path u)) ≡⟨ refl ⟩
        -- sym (cong f1 (path u)) ≡⟨ cong sym (pathToEM u) ⟩
        -- sym (emloop [ u ])     ≡⟨ sym (emloop-sym ∣ P ∣ [ u ]) ⟩
        -- emloop [ inv u ]       ∎
      -- -- cong f1 (assoc (path u) (path v) (path w) i) ≡ emloop [ FG.assoc u v w i ]
      -- pathToEM (FG.assoc u v w i) = emsquash _ _ _ _ {!!} {!!} i
      -- --- cong f1 (rUnit (path u) i) ≡ emloop [ idr u i ]
      -- pathToEM (idr u i) = lem i
        -- where
        -- lem : PathP (λ i → cong f1 (path (idr u i)) ≡ emloop [ idr u i ]) (pathToEM u) (pathToEM (u · ε))
        -- lem = toPathP (emsquash _ _ _ _ _ _)
      -- pathToEM (idl u i) = {!!}
      -- pathToEM (invr u i) = {!!}
      -- pathToEM (invl u i) = {!!}
      -- pathToEM (trunc u v p q i j) = {!!}

      pathToEM : (u : ⟨ P * ⟩) → cong f1 (path u) ≡ emloop [ u ]
      pathToEM = FG.elimProp
        {B = λ u → cong f1 (path u) ≡ emloop [ u ]}
        (λ _ → emsquash _ _ _ _)
        (λ a → refl)
        (λ u v p q → 
           cong f1 (path u ∙ path v)                     ≡⟨ cong-∙ f1 (path u) (path v) ⟩
           cong f1 (path u) ∙ cong f1 (path v)           ≡⟨ cong₂ _∙_ (pathToEM u) (pathToEM v) ⟩
           emloop [ u ] ∙ emloop [ v ]                   ≡⟨ sym (emloop-comp ∣ P ∣ [ u ] [ v ]) ⟩
           emloop (GroupStr._·_ (snd ∣ P ∣) [ u ] [ v ]) ≡⟨ refl ⟩
           emloop [ u · v ]                              ∎
        )
        (sym (emloop-1g ∣ P ∣))
        (λ u p → 
           cong f1 (sym (path u)) ≡⟨ refl ⟩
           sym (cong f1 (path u)) ≡⟨ cong sym (pathToEM u) ⟩
           sym (emloop [ u ])     ≡⟨ sym (emloop-sym ∣ P ∣ [ u ]) ⟩
           emloop [ inv u ]       ∎
        )

      f : Delooping → EM₁ ∣ P ∣
      f (inj x) = f1 x
      f (rel r i j) = lem i j
        where
        u = src (snd P) r
        v = tgt (snd P) r
        lem : cong f1 (path u) ≡ cong f1 (path v)
        lem = pathToEM u ∙ cong emloop (eq/ _ _ (fcBase r)) ∙ sym (pathToEM v)
      f (gpd x y p q P Q i j k) = emsquash (f x) (f y) (cong f p) (cong f q) (λ i j → f (P i j)) (λ i j → f (Q i j)) i j k

      g : EM₁ ∣ P ∣ → Delooping
      g = EM.elimGroupoid
        ∣ P ∣
        (λ _ → gpd)
        (inj ⋆)
        -- this is where we need the section
        (λ u → cong inj (path (sec u)))
        (λ u v → toPathP (lem u v))
        where
        -- lem : (u v : fst ∣ P ∣) → transport (λ i → inj (path (sec u) i) ≡ inj (path (sec ((snd ∣ P ∣ GroupStr.· u) v)) i)) (λ _ → inj ⋆) ≡ (λ i → inj (path (sec v) i))
        lem : (u v : fst ∣ P ∣) → subst2 _≡_ (cong inj (path (sec u))) (cong inj (path (sec (GroupStr._·_ (snd ∣ P ∣) u v )))) refl ≡ cong inj (path (sec v))
        lem u v =
          subst2 _≡_ (cong inj (path (sec u))) (cong inj (path (sec (GroupStr._·_ (snd ∣ P ∣) u v)))) refl ≡⟨ subst2≡Refl _ _ ⟩
          sym (cong inj (path (sec u))) ∙ cong inj (path (sec (GroupStr._·_ (snd ∣ P ∣) u v)))             ≡⟨ {!!} ⟩
          sym (cong inj (path (sec u))) ∙ cong inj (path (sec u · sec v))                                  ≡⟨ refl ⟩
          sym (cong inj (path (sec u))) ∙ cong inj (path (sec u) ∙ path (sec v))                           ≡⟨ cong₂ _∙_ refl (cong-∙ inj (path (sec u)) (path (sec v))) ⟩
          sym (cong inj (path (sec u))) ∙ cong inj (path (sec u)) ∙ cong inj (path (sec v))                ≡⟨ assoc _ _ _ ⟩
          (sym (cong inj (path (sec u))) ∙ cong inj (path (sec u))) ∙ cong inj (path (sec v))              ≡⟨ cong₂ _∙_ (lCancel _) refl ⟩
          refl ∙ cong inj (path (sec v))                                                                   ≡⟨ sym (lUnit _) ⟩
          cong inj (path (sec v))                                                                          ∎
          where
          -- Note: we cannot expect sec to directly preserve product, only under path
          lem' : path (sec (GroupStr._·_ (snd ∣ P ∣) u v)) ≡ path (sec u · sec v)
          lem' = {!!}

      fg : (x : EM₁ ∣ P ∣) → f (g x) ≡ x
      fg = EM.elimSet ∣ P ∣ (λ x → emsquash (f (g x)) x)
        refl
        (λ x → toPathP (lem x))
        where
        -- lem : (x : fst ∣ P ∣) → transport (λ i → f1 (path (sec x) i) ≡ emloop x i) (λ _ → embase) ≡ (λ _ → embase)
        lem : (x : fst ∣ P ∣) → subst2 _≡_ (cong f1 (path (sec x))) (emloop x) refl ≡ refl
        lem x =
          subst2 _≡_ (cong f1 (path (sec x))) (emloop x) refl ≡⟨ subst2≡Refl (cong f1 (path (sec x))) (emloop x) ⟩
          sym (cong f1 (path (sec x))) ∙ emloop x             ≡⟨ cong₂ _∙_ (cong sym (pathToEM (sec x) ∙ cong emloop (isSec x))) refl ⟩
          sym (emloop x) ∙ emloop x                           ≡⟨ lCancel _ ⟩
          refl                                                ∎

      gf : (x : Delooping) → g (f x) ≡ x
      gf (inj ⋆) = refl
      gf (inj (gen a i)) j = lem j i
        where
        lem : cong g (emloop [ η a ]) ≡ cong inj (gen a)
        lem =
          cong g (emloop [ η a ])       ≡⟨ refl ⟩
          cong inj (path (sec [ η a ])) ≡⟨ {!!} ⟩
          cong inj (gen a)              ∎
      gf (rel r i j) = {!!}
      gf (gpd x y p q P Q i j k) = {!!} -- isPropIsGroupoid

      open Iso

      e : Iso Delooping (EM₁ ∣ P ∣)
      fun e = f
      Iso.inv e = g
      rightInv e = fg
      leftInv e = gf
