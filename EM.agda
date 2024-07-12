{-# OPTIONS --cubical #-}

--
-- Construction of a "smaller" variant of deloopings as Eilenberg-MacLane spaces
-- (K(G,1)) for a group G with a given presentation and equivalence with
-- traditional spaces.
--

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed hiding (⋆)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Relation.Binary hiding (Rel)
open import Cubical.HITs.SetQuotients as SQ

private variable
  ℓ ℓ' : Level

module _ (G : Group ℓ) where
  open GroupStr (str G)
  open import Cubical.HITs.EilenbergMacLane1 as EM

  -- An aside: preservation of identities is automatic in Eilenberg-MacLane spaces
  loop-id : emloop 1g ≡ refl
  loop-id =
    emloop 1g                              ≡⟨ lUnit (emloop 1g) ⟩
    refl ∙ emloop 1g                       ≡⟨ cong (_∙ emloop 1g) (sym (lCancel (emloop 1g)) ) ⟩
    (emloop 1g ⁻¹ ∙ emloop 1g) ∙ emloop 1g ≡⟨ sym (assoc _ _ _) ⟩
    emloop 1g ⁻¹ ∙ (emloop 1g ∙ emloop 1g) ≡⟨ cong (sym (emloop 1g) ∙_) (sym (emloop-comp G 1g 1g) ∙ cong emloop (·IdL 1g)) ⟩
    emloop 1g ⁻¹ ∙ emloop 1g               ≡⟨ rCancel _ ⟩
    refl                                   ∎

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

  module _ (R : Congruence) where

    -- Quotient of a group by a congruence
    quotient : Group ℓ
    quotient = (⟨ G ⟩ / fst R) , grp
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

    -- -- Quotient group morphism to the congruence
    -- quotientHom : GroupHom G quotient
    -- quotientHom = [_] , igh
      -- where
      -- open IsGroupHom
      -- igh : IsGroupHom _ [_] _
      -- pres· igh x y = refl
      -- pres1 igh = refl
      -- presinv igh x = refl

  -- Quotient of map by a relation
  quotientRec : (R : Graph {ℓ' = ℓ} ⟨ G ⟩) {H : Group ℓ} (f : GroupHom G H) → ((r : total R) → fst f (src R r) ≡ fst f (tgt R r)) → GroupHom (quotient (freeCongruenceCongruence R)) H
  quotientRec R {H} f rel = f/ , igh
    where
    isSetH : isSet ⟨ H ⟩
    isSetH = snd H .GroupStr.is-set
    R* = freeCongruenceCongruence R
    G/R* = quotient R*
    fR* : {x y : ⟨ G ⟩} (r : fst R* x y) → fst f x ≡ fst f y
    fR* (fcBase r) = rel r
    fR* fcRefl = refl
    fR* (fcTrans r s) = fR* r ∙ fR* s
    fR* (fcSym r) = sym (fR* r)
    fR* (fcProd r s) = f .snd .IsGroupHom.pres· _ _ ∙ cong₂ (snd H .GroupStr._·_) (fR* r) (fR* s) ∙ sym (f .snd .IsGroupHom.pres· _ _)
    f/ : ⟨ quotient R* ⟩ → ⟨ H ⟩
    f/ x = SQ.rec isSetH (fst f) (λ _ _ → fR*) x
    open IsGroupHom
    igh : IsGroupHom (snd G/R*) f/ (snd H)
    pres· igh x y = SQ.elimProp2
      {P = λ x y → f/ (snd G/R* .GroupStr._·_ x y) ≡ snd H .GroupStr._·_ (f/ x) (f/ y)}
      (λ _ _ → isSetH _ _)
      (snd f .pres·)
      x y
    pres1 igh = snd f .pres1
    presinv igh x = SQ.elimProp
      {P = λ x → f/ (snd G/R* .GroupStr.inv x) ≡ snd H .GroupStr.inv (f/ x)}
      (λ x → isSetH _ _)
      (snd f .presinv)
      x

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

  -- Operations on ∣ P ∣
  1P   = GroupStr.1g (str ∣ P ∣)
  _·P_ = GroupStr._·_ (str ∣ P ∣)
  invP = GroupStr.inv (str ∣ P ∣)

  -- The type of relations in the presentation
  Rel = total

  -- -- Non-dependent elimination from the presented group
  -- ∣P∣-rec : {G : Group ℓ}
    -- (f : ⟨ P ⟩ → ⟨ G ⟩) →
    -- ((r : Rel) → let f* = FG.rec {Group = G} f .fst in f* (src r) ≡ f* (tgt r)) →
    -- GroupHom ∣ P ∣ G
  -- ∣P∣-rec {G} f rel = f' , f'isHom
    -- where
    -- open Span
    -- f*hom : GroupHom (P *) G
    -- f*hom = FG.rec {Group = G} f
    -- f* : ⟨ P * ⟩ → ⟨ G ⟩
    -- f* = fst f*hom
    -- rel* : {u v : ⟨ P * ⟩} → (fst (freeCongruenceCongruence (P *) (str P)) u v) → f* u ≡ f* v
    -- rel* (fcBase r) = rel r
    -- rel* fcRefl = refl
    -- rel* (fcTrans r r') = rel* r ∙ rel* r' 
    -- rel* (fcSym r) = sym (rel* r)
    -- rel* (fcProd {u} {u'} {v} {v'} r r') = pres· u v ∙ cong₂ ((str G) .GroupStr._·_) (rel* r) (rel* r') ∙ sym (pres· u' v')
      -- where
      -- open IsGroupHom (snd f*hom)
    -- f' : ⟨ ∣ P ∣ ⟩ → ⟨ G ⟩
    -- f' = SQ.rec (GroupStr.is-set (str G)) f* (λ _ _ r → rel* r)
    -- open IsGroupHom
    -- f'isHom : IsGroupHom (str ∣ P ∣) f' (str G)
    -- pres· f'isHom = SQ.elimProp2 (λ _ _ → GroupStr.is-set (str G) _ _) (pres· (snd f*hom))
    -- pres1 f'isHom = pres1 (snd f*hom)
    -- presinv f'isHom = SQ.elimProp (λ _ → GroupStr.is-set (str G) _ _) (presinv (snd f*hom))

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

  -- Group structure on the loop space of the 1-delooping
  Ω1Delooping : Group ℓ
  Ω1Delooping = makeGroup {G = ⋆ ≡ ⋆} refl _∙_ sym (isGroupoid1Delooping ⋆ ⋆) assoc (λ p → sym (rUnit p)) (λ p → sym (lUnit p)) rCancel lCancel

  -- Extension of gen to paths
  gen* : GroupHom (P *) Ω1Delooping
  gen* = FG.rec gen

  -- Path associated to a formal composite
  path : (u : ⟨ P * ⟩) → ⋆ ≡ ⋆
  path = fst gen*

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
  theorem : Delooping ≃ EM₁ ∣ P ∣
  theorem = isoToEquiv e
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
         cong f1 (path u) ∙ cong f1 (path v)           ≡⟨ cong₂ _∙_ p q ⟩
         emloop [ u ] ∙ emloop [ v ]                   ≡⟨ sym (emloop-comp ∣ P ∣ [ u ] [ v ]) ⟩
         emloop (GroupStr._·_ (snd ∣ P ∣) [ u ] [ v ]) ≡⟨ refl ⟩
         emloop [ u · v ]                              ∎
      )
      (sym (emloop-1g ∣ P ∣))
      (λ u p → 
         cong f1 (sym (path u)) ≡⟨ refl ⟩
         sym (cong f1 (path u)) ≡⟨ cong sym p ⟩
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

    -- The loop space of a groupoid is a group
    Ωgroup : {ℓ : Level} (A : Pointed ℓ) → isGroupoid ⟨ A ⟩ → Group ℓ
    Ωgroup A Gpd = makeGroup {G = pt A ≡ pt A} refl (λ p q → p ∙ q) sym (Gpd _ _) GL.assoc (λ p → sym (GL.rUnit p)) (λ p → sym (GL.lUnit p)) GL.rCancel GL.lCancel

    -- Loop space of the reduced delooping
    ΩBP : Group ℓ
    ΩBP = Ωgroup (Delooping , inj ⋆) gpd

    -- inj as a group morphism
    injGrp : GroupHom Ω1Delooping ΩBP
    injGrp = (cong inj) , igh
      where
      open IsGroupHom
      igh : IsGroupHom (snd Ω1Delooping) (cong inj) (snd ΩBP)
      pres· igh = cong-∙ inj
      pres1 igh = refl
      presinv igh p = refl

    -- Loop associated to any element of the reduced delooping
    loopHom : GroupHom (∣ P ∣) ΩBP
    loopHom = quotientRec _ (str P) (compGroupHom gen* injGrp) rel

    -- Loop associated to any element of the presented group
    loop : ⟨ ∣ P ∣ ⟩ → ⟨ ΩBP ⟩
    loop = fst loopHom

    -- The above construction sends products to concatenation
    loop· : (u v : ⟨ ∣ P ∣ ⟩) → loop (u ·P v) ≡ loop u ∙ loop v
    loop· = IsGroupHom.pres· (snd loopHom)

    -- We can send EM to the delooping
    g : EM₁ ∣ P ∣ → Delooping
    g = EM.elimGroupoid
      ∣ P ∣
      (λ _ → gpd)
      (inj ⋆)
      (λ u → loop u)
      (λ u v → toPathP (lem u v))
      where
      lem : (u v : ⟨ ∣ P ∣ ⟩) → transport (λ i → loop u i ≡ loop (u ·P v) i) refl ≡ loop v
      lem u v =
        transport (λ i → loop u i ≡ loop (u ·P v) i) refl ≡⟨ subst2≡ (loop u) (loop (u ·P v)) refl ⟩
        sym (loop u) ∙ refl ∙ loop (u ·P v)               ≡⟨ cong (λ p → sym (loop u) ∙ p) (sym (lUnit _)) ⟩
        sym (loop u) ∙ loop (u ·P v)                      ≡⟨ cong (λ p → sym (loop u) ∙ p) (loop· u v) ⟩
        sym (loop u) ∙ (loop u ∙ loop v)                  ≡⟨ assoc _ _ _ ⟩
        (sym (loop u) ∙ loop u) ∙ loop v                  ≡⟨ cong (λ p → p ∙ loop v) (lCancel (loop u)) ⟩
        refl ∙ loop v                                     ≡⟨ sym (lUnit (loop v)) ⟩
        loop v                                            ∎

    fg : (x : EM₁ ∣ P ∣) → f (g x) ≡ x
    fg = EM.elimSet ∣ P ∣ (λ x → emsquash (f (g x)) x) refl λ x → toPathP (lem x)
      where
      lem' : (x : ⟨ ∣ P ∣ ⟩) → cong f (loop x) ≡ emloop x
      lem' = SQ.elimProp (λ _ → emsquash _ _ _ _) word
        where
        word : (u : ⟨ P * ⟩) → cong f (loop [ u ]) ≡ emloop [ u ]
        word = FG.elimProp
          (λ _ → emsquash _ _ _ _)
          (λ _ → refl)
          (λ u v p q → 
            cong f (loop [ u · v ])                   ≡⟨ refl ⟩
            cong f (loop ([ u ] ·P [ v ]))            ≡⟨ cong (cong f) (loop· [ u ] [ v ]) ⟩
            cong f (loop [ u ] ∙ loop [ v ])          ≡⟨ cong-∙ f (loop [ u ]) (loop [ v ]) ⟩
            cong f (loop [ u ]) ∙ cong f (loop [ v ]) ≡⟨ cong₂ _∙_ p q ⟩
            emloop [ u ] ∙ emloop [ v ]               ≡⟨ sym (emloop-comp _ [ u ] [ v ]) ⟩
            emloop ([ u ] ·P [ v ])                   ≡⟨ refl ⟩
            emloop [ u · v ]                          ∎
          )
          (sym (emloop-1g ∣ P ∣))
          (λ u p → 
            cong f (loop [ inv u ])                 ≡⟨ refl ⟩
            cong f (loop (invP [ u ]))              ≡⟨ refl ⟩
            cong f (sym (loop [ u ]))               ≡⟨ refl ⟩
            sym (cong f (loop [ u ]))               ≡⟨ cong sym p ⟩
            sym (emloop [ u ])                      ≡⟨ sym (emloop-sym _ [ u ]) ⟩
            emloop (invP [ u ])                     ≡⟨ refl ⟩
            emloop [ inv u ]                        ∎
          )
      lem : (x : ⟨ ∣ P ∣ ⟩) → subst2 _≡_ (cong (f ∘ g) (emloop x)) (emloop x) refl ≡ refl
      lem x =
        subst2 _≡_ (cong (f ∘ g) (emloop x)) (emloop x) refl ≡⟨ subst2≡Refl (cong (f ∘ g) (emloop x)) (emloop x) ⟩
        sym (cong (f ∘ g) (emloop x)) ∙ emloop x             ≡⟨ refl ⟩
        sym (cong f (cong g (emloop x))) ∙ emloop x          ≡⟨ refl ⟩
        sym (cong f (loop x)) ∙ emloop x                     ≡⟨ cong₂ _∙_ (cong sym (lem' x)) refl ⟩
        sym (emloop x) ∙ emloop x                            ≡⟨ lCancel _ ⟩
        refl                                                 ∎

    gf : (x : Delooping) → g (f x) ≡ x
    gf = Delooping-elim (λ x → g (f x) ≡ x) refl gf-gen gf-rel (λ x → isSet→isGroupoid (gpd (g (f x)) x))
      where
      gf-gen' : (a : ⟨ P ⟩) → cong g (emloop [ η a ]) ≡ cong inj (gen a)
      gf-gen' a =
        cong g (emloop [ η a ]) ≡⟨ refl ⟩
        loop [ η a ]            ≡⟨ refl ⟩
        cong inj (gen a)        ∎
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
