{-# OPTIONS --cubical #-}

--
-- Construction of a "smaller" variant of deloopings as Eilenberg-MacLane spaces
-- (K(G,1)) for a group G with a given presentation and equivalence with
-- traditional spaces.
--

open import Cubical.Foundations.Everything hiding (⋆)
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Data.Sigma
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Relation.Binary hiding (Rel)
open import Cubical.HITs.SetQuotients as SQ

private variable
  ℓ ℓ' : Level

-- Variant of substInPaths
subst2≡ : {A : Type ℓ} {x x' y y' : A} (p : x ≡ x') (q : y ≡ y') (r : x ≡ y) → subst2 _≡_ p q r ≡ sym p ∙ r ∙ q
subst2≡ p q r = J (λ _ p → subst2 _≡_ p q r ≡ sym p ∙ r ∙ q) lem p
  where
  lem'' : subst2 _≡_ refl refl r ≡ r
  lem'' = transportRefl r 
  lem' : subst2 _≡_ refl q r ≡ r ∙ q
  lem' = J (λ _ q → subst2 _≡_ refl q r ≡ r ∙ q) (lem'' ∙ rUnit r) q
  lem : subst2 _≡_ refl q r ≡ sym refl ∙ r ∙ q
  lem = lem' ∙ cong₂ _∙_ (lUnit r) refl ∙ sym (assoc _ _ _)

-- Useful case of subst2≡ where r is refl
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

-- A graph is a span endomorphism
Graph : (X : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Graph {ℓ' = ℓ'} X = Span {ℓ' = ℓ'} X X

module _ (G : Group ℓ) where
  open Span
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
  open Span (str P)

  -- The type of relations in the presentation
  Rel = total

  -- 1-skeleton of the delooping of a presentation
  data 1Delooping : Type ℓ where
    ⋆ : 1Delooping
    gen : (a : ⟨ P ⟩) → ⋆ ≡ ⋆

  -- Elimination principle for the 1-delooping
  1Delooping-elim :
    (A : 1Delooping → Type ℓ)
    (Apt : A ⋆) →
    ((a : ⟨ P ⟩) → PathP (λ i → cong A (gen a) i) Apt Apt) →
    (x : 1Delooping) → A x
  1Delooping-elim A Apt Agen ⋆ = Apt
  1Delooping-elim A Apt Agen (gen a i) = Agen a i

  postulate
    -- The 1-delooping is a groupoid when we have a set of generators. This is
    -- non-trivial and proved in Wärn's _Path spaces of pushouts_.
    isGroupoid1Delooping : isGroupoid 1Delooping

  -- Path associated to a formal composite
  -- Morally, we should be able to define it as
  -- -- path : (u : ⟨ P * ⟩) → ⋆ ≡ ⋆
  -- -- path = fst (FG.rec gen)
  -- but we would need the group structure on the loop space of the 1-delooping
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
    rel : (r : Rel) → cong inj (path (src r)) ≡ cong inj (path (tgt r))
    gpd : isGroupoid Delooping

  -- Dependent version of path 
  pathD :
    (A : Delooping → Type ℓ)
    (Apt : A (inj ⋆))
    (Agen : (a : ⟨ P ⟩) → PathP (λ i → A (inj (gen a i))) Apt Apt) →
    (u : ⟨ P * ⟩) → PathP (λ i → A (inj (path u i))) Apt Apt
  pathD A Apt Agen u = cong (1Delooping-elim (λ x → A (inj x)) Apt Agen) (path u)

  -- Elimination principle for the delooping
  Delooping-elim :
    (A : Delooping → Type ℓ)
    (Apt : A (inj ⋆))
    (Agen : (a : ⟨ P ⟩) → PathP (λ i → A (inj (gen a i))) Apt Apt)
    (Arel : (r : Rel) → PathP (λ i → PathP (λ j → A (rel r i j)) Apt Apt) (pathD A Apt Agen (src r)) (pathD A Apt Agen (tgt r))) →
    ((x : Delooping) → isGroupoid (A x)) → (x : Delooping) → A x
  Delooping-elim A Apt Agen Arel Agpd (inj x) = 1Delooping-elim (λ x → A (inj x)) Apt Agen x
  Delooping-elim A Apt Agen Arel Agpd (rel r i j) = Arel r i j
  Delooping-elim A Apt Agen Arel Agpd (gpd x y p q P Q i j k) = isOfHLevel→isOfHLevelDep 3 Agpd (f x) (f y) (cong f p) (cong f q) (cong (cong f) P) (cong (cong f) Q) (gpd x y p q P Q) i j k
    where
    f = Delooping-elim A Apt Agen Arel Agpd

  open import Cubical.HITs.EilenbergMacLane1 as EM

  -- Our main theorem: the delooping associated to the presentation coincides
  -- with the delooping as generic Eilenberg-MacLane spaces.
  --
  -- The termination checker does not manage to check termination in pathToEM,
  -- but it should
  {-# TERMINATING #-}
  theorem :
    -- We have a section
    (sec : fst ∣ P ∣ → ⟨ P * ⟩) →
    ((x : fst ∣ P ∣) → [ sec x ] ≡ x) →
    -- which preserves generators
    ((a : ⟨ P ⟩) → path (sec [ η a ]) ≡ gen a) →
    -- and products
    ((u v : fst ∣ P ∣) → path (sec (GroupStr._·_ (snd ∣ P ∣) u v)) ≡ path (sec u · sec v)) →
    Delooping ≃ EM₁ ∣ P ∣
  theorem sec isSec secGen secProd = isoToEquiv e
    where

    -- We cen send the 1-delooping to EM
    f1 : 1Delooping → EM₁ ∣ P ∣
    f1 ⋆ = embase
    f1 (gen a i) = emloop [ η a ] i

    -- The extension of f1 to paths coincides with the canonical embedding
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

    -- For every base relation the source and target paths are equal in the EM-space
    f1rel : (r : Rel) → cong f1 (path (src r)) ≡ cong f1 (path (tgt r))
    f1rel r = pathToEM (src r) ∙ cong emloop (eq/ _ _ (fcBase r)) ∙ sym (pathToEM (tgt r))

    -- We can send the delooping to EM
    f : Delooping → EM₁ ∣ P ∣
    f (inj x) = f1 x
    f (rel r i j) = f1rel r i j
    f (gpd x y p q P Q i j k) = emsquash (f x) (f y) (cong f p) (cong f q) (λ i j → f (P i j)) (λ i j → f (Q i j)) i j k

    -- We can send EM to the delooping
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
        sym (cong inj (path (sec u))) ∙ cong inj (path (sec (GroupStr._·_ (snd ∣ P ∣) u v)))             ≡⟨ cong₂ _∙_ refl (cong (cong inj) (secProd u v)) ⟩
        sym (cong inj (path (sec u))) ∙ cong inj (path (sec u · sec v))                                  ≡⟨ refl ⟩
        sym (cong inj (path (sec u))) ∙ cong inj (path (sec u) ∙ path (sec v))                           ≡⟨ cong₂ _∙_ refl (cong-∙ inj (path (sec u)) (path (sec v))) ⟩
        sym (cong inj (path (sec u))) ∙ cong inj (path (sec u)) ∙ cong inj (path (sec v))                ≡⟨ assoc _ _ _ ⟩
        (sym (cong inj (path (sec u))) ∙ cong inj (path (sec u))) ∙ cong inj (path (sec v))              ≡⟨ cong₂ _∙_ (lCancel _) refl ⟩
        refl ∙ cong inj (path (sec v))                                                                   ≡⟨ sym (lUnit _) ⟩
        cong inj (path (sec v))                                                                          ∎

    fg : (x : EM₁ ∣ P ∣) → f (g x) ≡ x
    fg = EM.elimSet ∣ P ∣ (λ x → emsquash (f (g x)) x)
      refl
      (λ x → toPathP (lem x))
      where
      lem : (x : fst ∣ P ∣) → subst2 _≡_ (cong f1 (path (sec x))) (emloop x) refl ≡ refl
      lem x =
        subst2 _≡_ (cong f1 (path (sec x))) (emloop x) refl ≡⟨ subst2≡Refl (cong f1 (path (sec x))) (emloop x) ⟩
        sym (cong f1 (path (sec x))) ∙ emloop x             ≡⟨ cong₂ _∙_ (cong sym (pathToEM (sec x) ∙ cong emloop (isSec x))) refl ⟩
        sym (emloop x) ∙ emloop x                           ≡⟨ lCancel _ ⟩
        refl                                                ∎

    gf : (x : Delooping) → g (f x) ≡ x
    gf = Delooping-elim (λ x → g (f x) ≡ x)
      refl
      gf-gen
      gf-rel
      (λ x → isSet→isGroupoid (gpd (g (f x)) x))
      where
      gf-gen' : (a : ⟨ P ⟩) → cong g (emloop [ η a ]) ≡ cong inj (gen a)
      gf-gen' a =
        cong g (emloop [ η a ])       ≡⟨ refl ⟩
        cong inj (path (sec [ η a ])) ≡⟨ cong (cong inj) (secGen a) ⟩
        cong inj (gen a)              ∎
      gf-gen : (a : ⟨ P ⟩) → PathP (λ i → g (f1 (gen a i)) ≡ inj (gen a i)) refl refl
      gf-gen a i j = gf-gen' a j i
      gf-rel' : (r : Rel) → Cube
        (pathD (λ x → g (f x) ≡ x) refl gf-gen (src r))
        (pathD (λ x → g (f x) ≡ x) refl gf-gen (tgt r))
        refl
        refl
        (cong (cong g) (f1rel r))
        (rel r)
      gf-rel' r = isGroupoid→isGroupoid' gpd _ _ _ _ _ _
      gf-rel : (r : Rel) →
        PathP (λ i → PathP (λ j → g (f1rel r i j) ≡ rel r i j) refl refl)
          (pathD (λ x → g (f x) ≡ x) refl gf-gen (src r))
          (pathD (λ x → g (f x) ≡ x) refl gf-gen (tgt r))
      gf-rel r = gf-rel' r
    open Iso

    e : Iso Delooping (EM₁ ∣ P ∣)
    fun e = f
    Iso.inv e = g
    rightInv e = fg
    leftInv e = gf

    -- Note: we never use any hypothesis on the hLevel of the presentation (the
    -- type of generators and relations do not need to be sets).
