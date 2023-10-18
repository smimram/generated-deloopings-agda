{-

  This file contains:

  - The forgetful functor U from GSets to XSets when X is a subset of G
  - Proof that the the loop space of the principal torsor is invariant by U.

  -}

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.FreeGroup renaming (_·_ to _·f_)

open import XSet
open import GSet
open import GSetProperties
open import Generators
open import PrincipalTorsor


private
  variable
    ℓ : Level

-- A natural forgetful functor for subsets of groups:
U : {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} → GSet ℓ G → XSet ℓ X
U {G = G} {X = X} {ι = ι} (A , strA) = A , xsetstr (action ϕ∘ι  isSetA)
  where
  isSetA = strA .GSetStr.is-set
  ϕ = strA .GSetStr._*_
  ϕ∘ι : ⟨ X ⟩ → A → A
  ϕ∘ι x a = ϕ (ι x) a

postulate
  theorem1 : {G : Group ℓ} {A B : GSet ℓ G} → (A ≡ B) ≃ (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((g : ⟨ G ⟩) (a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a)))
  theorem2 : {X : hSet ℓ} {A B : XSet ℓ X} → (A ≡ B) ≃ (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((x : ⟨ X ⟩) (a : ⟨ A ⟩) → transport p ((str A .XSetStr._*_) x a) ≡ (str B .XSetStr._*_) x (transport p a)))
  theorem3 : {G : Group ℓ} {A B : GSet ℓ G} {p : ⟨ A ⟩ ≡ ⟨ B ⟩} {g : ⟨ G ⟩} → isProp ((a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a))
  theorem4 : {A : Type ℓ} {P : A → Type ℓ} → ((x : A) → ∥ P x ∥₁) → ∥ ((y : A) → P y) ∥₁

module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  open GroupStr (str G)
  open principal-torsor {G = G}
  open generators {G = G} {X = X} {ι = ι}
  module _ {generates : ι-generates} where
    thm : Iso (PG ≡ PG) (U PG ≡ U PG)
    Iso.fun thm eq = invEq (theorem2 {X = X}) (p , λ x a → comm (ι x) a)
      where
      t = equivFun theorem1 eq
      p = fst t
      comm = snd t
    Iso.inv thm eq = invEq theorem1 (p , comm-star)
      where
      t = equivFun theorem2 eq
      p : ⟨ G ⟩ ≡ ⟨ G ⟩
      p = fst t
      comm = snd t
      comm-star : (g : ⟨ G ⟩) → (a : ⟨ G ⟩) → (transport p (g · a)) ≡ (g · (transport p a))
      comm-star g = Cubical.HITs.PropositionalTruncation.rec (theorem3 {p = p} {g = g}) lem (generates g)
        where
        lem : (Σ (FreeGroup ⟨ X ⟩) λ x → (ι-star-hom .fst x ≡ g)) → ((a : ⟨ G ⟩) → transport p (g · a) ≡ g · (transport p a))
        lem (x , prf) a =
          transport p (g · a)                       ≡⟨ {!!} ⟩ -- prf
          transport p ((ι-star-hom .fst x)  · a)     ≡⟨ {!!} ⟩
          (ι-star-hom .fst x) · (transport p a)      ≡⟨ {!!} ⟩  -- prf
          g · (transport p a) ∎


    Iso.rightInv thm = {!!}
    Iso.leftInv thm = {!!}
