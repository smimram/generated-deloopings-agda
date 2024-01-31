{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Relation.Binary
open import Cubical.HITs.SetQuotients as SQ

private variable
  ℓ ℓ' : Level

record Span (X Y : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    total : Type ℓ'
    src : total → X
    tgt : total → Y

open Span public

Graph : (X : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Graph {ℓ' = ℓ'} X = Span {ℓ' = ℓ'} X X

module _ (G : Group ℓ) where
  open GroupStr (str G)

  record isCongruence (_∼_ : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ) : Type ℓ where
    field
      equivalence : BinaryRelation.isEquivRel _∼_
      preservesProd : {x x' y y' : ⟨ G ⟩} → x ∼ x' → y ∼ y' → (x · y) ∼ (x' · y')
      -- preservesInverse : {x y : ⟨ G ⟩} → x ∼ y → inv x ∼ inv y

  open isCongruence public

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
    -- The free congruence on a relation
    data freeCongruence : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ where
      fcBase : (r : total R) → freeCongruence (src R r) (tgt R r)
      -- fcCong : isCongruence (freeCongruence R)
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

  quotient : Congruence → Group ℓ
  quotient R = (⟨ G ⟩ / fst R) , grp
    where
    open isCongruence (snd R)
    grp : GroupStr (⟨ G ⟩ / fst R)
    GroupStr.1g grp = [ 1g ]
    GroupStr._·_ grp x y = rec2 squash/ (λ x y → [ x · y ]) (λ _ _ _ r → {!!}) (λ _ _ _ r → {!!}) x y
    GroupStr.inv grp x = SQ.rec squash/ (λ x → [ inv x ]) (λ _ _ r → eq/ _ _ (preservesInverse R r)) x
    GroupStr.isGroup grp = {!!}

open import Cubical.HITs.FreeGroup as FG

Presentation : {ℓ : Level} → Type _
Presentation {ℓ} = TypeWithStr ℓ (λ X → Graph {ℓ' = ℓ} (FreeGroup X))

∣_∣ : {ℓ : Level} → Presentation {ℓ} → Group ℓ
∣ P ∣ = quotient P* (freeCongruenceCongruence P* (str P))
  where
  P* = freeGroupGroup ⟨ P ⟩
