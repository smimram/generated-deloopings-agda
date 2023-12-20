{-

  This file contains:

  - Definition of GSet Homomorphisms
  - Definition of GSetEquiv : GSet Isomorphisms

-}

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Reflection.RecordEquiv

open import GSet

private
  variable
    ℓ : Level

-- This lemma is probably part of the standard library somewhere: it states that
-- in order to show the equality p ≡ q of two paths between types is it enough
-- to show that the corresponding equivalences are equal
pathEq : {A B : Type ℓ} {p q : A ≡ B} → transport p ≡ transport q → p ≡ q
pathEq {p = p} {q = q} t = isEmbedding→Inj (isEquiv→isEmbedding (snd univalence)) p q (equivEq t)
  where
  open import Cubical.Foundations.Equiv
  open import Cubical.Functions.Embedding

-- TODO: can the Levels be different ?
record IsGSetHom {G : Group ℓ} {X Y : Type ℓ} (M : GSetStr G X)  (f : X → Y) (N : GSetStr G Y)
  : Type ℓ
  where

  -- shorter qualified names
  private
    module M = GSetStr M
    module N = GSetStr N

  field
    pres* : (g : ⟨ G ⟩) (x : X ) → f (g M.* x) ≡ g N.* (f x)

unquoteDecl IsGSetHomIsoΣ = declareRecordIsoΣ IsGSetHomIsoΣ (quote IsGSetHom)

module _ {G : Group ℓ} {X : Type ℓ} {Y : Type ℓ} {M : GSetStr {ℓ} G X} {f : X → Y} {N : GSetStr {ℓ} G Y}
  (pres : (g : ⟨ G ⟩) (x : X) → f ((GSetStr._*_ M) g x) ≡ (GSetStr._*_ N) g (f x))
  where

  makeIsGSetHom : IsGSetHom M f N
  makeIsGSetHom .IsGSetHom.pres* = pres

module _ {G : Group ℓ} where

  GSetHom : (X Y : GSet G) → Type ℓ
  GSetHom X Y = Σ[ f ∈ (⟨ X ⟩ → ⟨ Y ⟩) ] IsGSetHom (str X) f (str Y)

  isGSetEquiv : {X Y : Type ℓ} (M : GSetStr G X) (e : X ≃ Y) (N : GSetStr G Y) → Type ℓ
  isGSetEquiv M e N = IsGSetHom M (e .fst) N

  GSetEquiv : (X Y : GSet G) → Type ℓ
  GSetEquiv X Y = Σ[ e ∈ (⟨ X ⟩ ≃ ⟨ Y ⟩) ] isGSetEquiv (str X) e (str Y)

  makeIsGSetEquiv = makeIsGSetHom

  isPropIsGSetHom : {X Y : GSet G} {f : ⟨ X ⟩ → ⟨ Y ⟩} → isProp (IsGSetHom (str X) f (str Y))
  isPropIsGSetHom {X = X} {Y = Y} = isOfHLevelRespectEquiv 1 (invEquiv (isoToEquiv IsGSetHomIsoΣ)) (isPropΠ2 λ g x → ((str Y) .GSetStr.is-set) _ _)

  GSetIdEquiv : (X : GSet G) → GSetEquiv X X
  GSetIdEquiv X = idEquiv ⟨ X ⟩ , makeIsGSetEquiv λ x y → refl

  idToGSetEquiv : {X Y : GSet G} → X ≡ Y → GSetEquiv X Y
  idToGSetEquiv {X = X} = J (λ Y p → GSetEquiv X Y) (GSetIdEquiv X)

  idToGSetIdEquivRefl : {X : GSet G} → idToGSetEquiv refl ≡ GSetIdEquiv X
  idToGSetIdEquivRefl {X = X} = JRefl (λ Y p → GSetEquiv X Y) (GSetIdEquiv X)

  -- the underlying equivalence of idToGSetEquiv is pathToEquiv
  idToGSetEquivFst : {X Y : GSet G} (p : X ≡ Y) → fst (idToGSetEquiv p) ≡ pathToEquiv (cong fst p)
  idToGSetEquivFst {X} {Y} = J (λ Y p → fst (idToGSetEquiv p) ≡ pathToEquiv (cong fst p)) lem
    where
    lem =
      fst (idToGSetEquiv {X = X} refl) ≡⟨ cong fst (idToGSetIdEquivRefl {X = X}) ⟩
      fst (GSetIdEquiv X) ≡⟨ sym pathToEquivRefl ⟩
      pathToEquiv (refl {x = fst X}) ≡⟨ refl ⟩
      pathToEquiv (cong fst (refl {x = X})) ∎

  GSetEquiv≡ : {X Y : GSet G} {f g : GSetEquiv X Y} → equivFun (fst f) ≡ equivFun (fst g) → f ≡ g
  GSetEquiv≡ p = Σ≡Prop (λ _ → isPropIsGSetHom) (Σ≡Prop isPropIsEquiv p)

  GSetPath : (X Y : GSet G) → (GSetEquiv X Y) ≃ (X ≡ Y)
  GSetPath X Y = ∫ 𝒮ᴰ-GSet .UARel.ua X Y
    where
    open import Cubical.Displayed.Base
    open import Cubical.Displayed.Universe
    open import Cubical.Displayed.Record
    open import Cubical.Displayed.Auto

    𝒮ᴰ-GSet : DUARel (𝒮-Univ ℓ) (GSetStr G) ℓ
    𝒮ᴰ-GSet = 𝒮ᴰ-Record (𝒮-Univ _) isGSetEquiv (fields: data[ ϕ ∣ autoDUARel _ _ ∣ {!compat!} ])
      where
      open GSetStr
      open IsGSetHom
      -- (GSetHom.autoDUA DUARel.≅ᴰ⟨ ϕ r ⟩ e) (ϕ r')
      --  PathP
      -- (λ i →
         -- Action G
         -- (Agda.Builtin.Cubical.Glue.primGlue a
          -- (λ .x → (λ { (i = i0) → a , e ; (i = i1) → a , idEquiv a }) _ .fst)
          -- (λ .x →
             -- (λ { (i = i0) → a , e ; (i = i1) → a , idEquiv a }) _ .snd)))
      -- (ϕ r) (ϕ r')
      compat : {X X' : Type ℓ} {r : GSetStr G X} {e : X ≃ X'} {r' : GSetStr G X'} → isGSetEquiv r e r' → PathP {!!} (ϕ r) (ϕ r') 
      compat = {!pres*!}

  GSetUnivalence : {X Y : GSet G} → isEquiv (idToGSetEquiv {X = X} {Y = Y})
  GSetUnivalence {X} {Y} = {!!}
    where
    lem : (X ≡ Y) ≃ GSetEquiv X Y
    lem =
      X ≡ Y ≃⟨ {!!} ⟩
      GSetEquiv X Y ■

  GSetUA : {X Y : GSet G} → GSetEquiv X Y → X ≡ Y
  GSetUA {X} {Y} = invEq (_ , GSetUnivalence {X = X} {Y = Y})

  GSetUAβ : {X Y : GSet G} (f : GSetEquiv X Y) → idToGSetEquiv (GSetUA f) ≡ f
  GSetUAβ f = secEq (idToGSetEquiv , GSetUnivalence) f

  GSetUAη : {X Y : GSet G} (p : X ≡ Y) → GSetUA (idToGSetEquiv p) ≡ p
  GSetUAη p = retEq (idToGSetEquiv , GSetUnivalence) p

  GSetUAFst : {X Y : GSet G} (f : GSetEquiv X Y) → cong fst (GSetUA f) ≡ ua (fst f)
  GSetUAFst f = pathEq lem
    where
    lem =
      transport (cong fst (GSetUA f)) ≡⟨ refl ⟩
      subst fst (GSetUA f)            ≡⟨ {!!} ⟩
      equivFun (fst f)                ≡⟨ sym (funExt (λ x → uaβ (fst f) x)) ⟩
      transport (ua (fst f))          ∎
