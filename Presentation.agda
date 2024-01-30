{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.HITs.SetQuotients as SQ

private variable
  ℓ : Level

module _ (G : Group ℓ) where
  open GroupStr (str G)

  record isCongruence (_∼_ : ⟨ G ⟩ → ⟨ G ⟩ → Type ℓ) : Type ℓ where
    field
      isReflexive : {x : ⟨ G ⟩} → x ∼ x
      isTransitive : {x y z : ⟨ G ⟩} → x ∼ y → y ∼ z → x ∼ z
      isSymmetric : {x y : ⟨ G ⟩} → x ∼ y → y ∼ x
      preservesProduct : {x x' y y' : ⟨ G ⟩} → x ∼ x' → y ∼ y' → (x · y) ∼ (x' · y')
      preservesInverse : {x y : ⟨ G ⟩} → x ∼ y → inv x ∼ inv y

  Congruence : Type _
  Congruence = Σ (⟨ G ⟩ → ⟨ G ⟩ → Type ℓ) isCongruence

  quotient : Congruence → Group ℓ
  quotient R = (⟨ G ⟩ / fst R) , grp
    where
    open isCongruence (snd R)
    grp : GroupStr (⟨ G ⟩ / fst R)
    GroupStr.1g grp = [ 1g ]
    GroupStr._·_ grp x y = rec2 squash/ (λ x y → [ x · y ]) (λ _ _ _ r → {!!}) (λ _ _ _ r → {!!}) x y
    GroupStr.inv grp x = SQ.rec squash/ (λ x → [ inv x ]) (λ _ _ r → eq/ _ _ (preservesInverse r)) x
    GroupStr.isGroup grp = {!!}

open import Cubical.HITs.FreeGroup as FG

record Relation (X : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor relationstr
  field
    rel : Type ℓ
    src : rel → FreeGroup X
    tgt : rel → FreeGroup X

Presentation : {ℓ : Level} → Type _
Presentation {ℓ} = TypeWithStr ℓ Relation

∣_∣ : {ℓ : Level} → Presentation {ℓ} → Group ℓ
∣ P ∣ = {!!}
