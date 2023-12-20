{-

  This file contains:

  - Equality types for Actions and GSetHoms
  - Properties of GSetEquivs
  - Isomorphisms and paths are equivalent (through fundamental theorem of identity types)
  - Gsets form a groupoid

-}

{-# OPTIONS --cubical #-}

module GSetProperties where

open import Cubical.Foundations.Everything
open import Cubical.Algebra.Group
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv

open import GSet
open import GSetHom

private
  variable
    ℓ : Level

-- Actions that coincide are equal
equalActions : {G : Group ℓ} {X : Type ℓ} (ϕ ψ : Action G X) → ϕ .Action._*_ ≡ ψ .Action._*_ → ϕ ≡ ψ
equalActions {G} {X} ϕ ψ refl =  isoFunInjective  ActionIsoΣ ϕ ψ
  (ΣPathP (refl ,
    ΣPathP (isPropIsSet _ _ ,
      ΣPathP ( (funExt (λ _ → toPathP (ψ .Action.is-set _ _ _ _))) ,
      funExt λ _ →
        funExt λ _ →
          funExt λ _ → toPathP (ψ .Action.is-set _ _ _ _)))))

equalGSetStructures : {G : Group ℓ} {X : Type ℓ} (A B : GSetStr G X) → A .GSetStr._*_ ≡ B .GSetStr._*_ → A ≡ B
equalGSetStructures A B p = isoFunInjective GSetStrIsoΣ A B (equalActions _ _ p)

-- Use of this should be replaced by isPropIsGSetHom
equalIsGSetHom : {G : Group ℓ} {X Y : GSet G} {f : ⟨ X ⟩ → ⟨ Y ⟩} (hom hom' : IsGSetHom (str X) f (str Y)) → hom .IsGSetHom.pres* ≡ hom' .IsGSetHom.pres* → hom ≡ hom'
equalIsGSetHom {G = G} {X = X} {Y = Y} {f = f} hom hom' p = isoFunInjective  IsGSetHomIsoΣ hom hom' p

idGSetEquiv : {G : Group ℓ} {X : GSet G} → GSetEquiv X X
fst (idGSetEquiv {X = X}) = idEquiv ⟨ X ⟩
snd idGSetEquiv = makeIsGSetHom λ _ _ → refl

-- The reciprocal of an isomorphism is an isomorphism
isGSetHomInv : {G : Group ℓ} {X : GSet G} {Y : GSet G} (f : ⟨ X ⟩ ≃ ⟨ Y ⟩) → IsGSetHom (str X) (fst f) (str Y) → IsGSetHom (str Y) (invEq f) (str X)
isGSetHomInv {ℓ} {G} {X} {Y} (e , eEq) eHom = is-hom-h
  where
    h : ⟨ Y ⟩ → ⟨ X ⟩
    h = invEq (e , eEq)

    _⋆₁_ = GSetStr._*_ (str Y)
    _⋆₂_ = GSetStr._*_ (str X)

    sec : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → y ≡ e (h y)
    sec g y = sym (secEq ((e , eEq)) y)

    hom : (g : ⟨ G ⟩) (y : ⟨ Y ⟩) → g ⋆₁ e (h y) ≡ e (g ⋆₂ h y)
    hom g y = sym (IsGSetHom.pres* eHom g (h y))

    is-hom-h : IsGSetHom (str Y)  h (str X)
    IsGSetHom.pres* is-hom-h g y =
      h (g ⋆₁ y) ≡⟨ cong (λ y' → h (g ⋆₁ y'))  (sec g y) ⟩
      h (g ⋆₁ (e (h y))) ≡⟨ cong h (hom g y) ⟩
      h (e (g ⋆₂ (h y))) ≡⟨ retEq (e , eEq) _ ⟩
      g ⋆₂ (h y) ∎

open import Cubical.Foundations.Equiv.Fiberwise

decomposedEqualGSet : {G : Group ℓ} {A : GSet G} → Type _
decomposedEqualGSet {G = G} {A = A} = Σ (Σ (Type _) λ B → ⟨ A ⟩ ≃ B) λ { (B , e) →
                                       Σ (⟨ G ⟩ → B → B) (λ _*_ →
                                         Σ (isSet B) (λ SB →
                                           Σ ((x : B) → (str G).GroupStr.1g * x ≡ x) (λ unit →
                                             Σ ((g1 g2 : ⟨ G ⟩) (x : B) → g1 * (g2 * x) ≡ ((str G).GroupStr._·_ g1 g2) * x) (λ comp →
                                               IsGSetHom (str A) (equivFun e) (gsetstr (action _*_ SB unit comp))))))  }

-- theorem : {G : Group ℓ} {A B : GSet ℓ G} → (A ≡ B) ≃ (Σ (⟨ A ⟩ ≡ ⟨ B ⟩) λ p → ((g : ⟨ G ⟩) (a : ⟨ A ⟩) → transport p ((str A .GSetStr._*_) g a) ≡ (str B .GSetStr._*_) g (transport p a)))
-- theorem {G = G} {A = A} {B = B} = compEquiv (invEquiv ΣPath≃PathΣ) {!!}

GSetPath' : {G : Group ℓ} {X Y : GSet G} → (X ≡ Y) ≃ (GSetEquiv X Y)
GSetPath' {ℓ} {G} {X} {Y} = fundamentalTheoremOfId GSetEquiv (λ A → idGSetEquiv {X = A}) contr X Y
  where
  contr : (A : GSet G) → isContr (Σ (GSet G) (λ B → GSetEquiv A B))
  contr A = subst isContr (sym (ua lem)) lem'
    where
    lem : Σ (GSet G) (λ B → GSetEquiv A B) ≃ decomposedEqualGSet {G = G} {A = A}
    lem = compEquiv (Σ-cong-equiv-fst (Σ-cong-equiv-snd λ _ → isoToEquiv (compIso GSetStrIsoΣ ActionIsoΣ))) (compEquiv (compEquiv Σ-assoc-≃ (Σ-cong-equiv-snd λ _ → compEquiv (invEquiv Σ-assoc-≃) (compEquiv (Σ-cong-equiv-fst Σ-swap-≃) Σ-assoc-≃))) (compEquiv (invEquiv Σ-assoc-≃) (Σ-cong-equiv-snd λ _ → compEquiv Σ-assoc-≃ (Σ-cong-equiv-snd λ _ → compEquiv Σ-assoc-≃ (Σ-cong-equiv-snd λ _ → Σ-assoc-≃)))))
    isContrSingl≃ : (A : Type ℓ) → isContr (Σ (Type ℓ) λ B → A ≃ B)
    isContrSingl≃ A = (A , idEquiv A) , λ { (B , e) → ΣPathP (ua e , toPathP (tsp (ua e) ∙ pathToEquiv-ua e)) }
      where
      tsp : {B : Type ℓ} (p : A ≡ B) → subst (λ B → A ≃ B) p (idEquiv A) ≡ pathToEquiv p
      tsp = J (λ B p → subst (λ B → A ≃ B) p (idEquiv A) ≡ pathToEquiv p) (sym (pathToEquivRefl ∙ sym (substRefl {B = λ B → A ≃ B} (idEquiv A))))
    lem' : isContr (decomposedEqualGSet {G = G} {A = A})
    lem' = isContrΣ (isContrSingl≃ ⟨ A ⟩) (λ (B , e) → lem'' B e)
      where
      lem'' : (B : Type ℓ) (e : ⟨ A ⟩ ≃ B) → isContr ( Σ (⟨ G ⟩ → B → B) (λ _*_ →
                                                         Σ (isSet B) (λ SB →
                                                           Σ ((x : B) → (str G).GroupStr.1g * x ≡ x) (λ unit →
                                                             Σ ((g1 g2 : ⟨ G ⟩) (x : B) → g1 * (g2 * x) ≡ ((str G).GroupStr._·_ g1 g2) * x) (λ comp →
                                                               IsGSetHom (str A) (equivFun e) (gsetstr (action _*_ SB unit comp)))))))
      lem'' B e = (_*'_ , SB' , unit' , comp' , hom') , unique
        where
        open GSetStr (str A)
        SA = (str A) .GSetStr.is-set
        open GroupStr (str G)
        f = equivFun e
        f⁻  = invEq e

        _*'_ : ⟨ G ⟩ → B → B
        _*'_ g x = f (g * (f⁻  x))
        SB' : isSet B
        SB' = isOfHLevelRespectEquiv 2 e SA
        unit' : (x : B) → (1g *' x) ≡ x
        unit' x =
          f (1g * (f⁻ x)) ≡⟨ cong (equivFun e) (·Unit _)  ⟩
          f (f⁻ x)        ≡⟨ secEq e x ⟩
          x               ∎
        comp' : (g1 g2 : ⟨ G ⟩) (x : B) → g1 *' (g2 *' x) ≡ (g1 · g2) *' x
        comp' g1 g2 x =
           f (g1 * (f⁻  (f (g2 * (f⁻  x))))) ≡⟨ cong (λ y → f (g1 * y)) (retEq e _) ⟩
           f (g1 * (g2 * (f⁻  x))) ≡⟨ cong f (·Composition g1 g2 _) ⟩
           f ((g1 · g2) * (f⁻  x)) ∎
        hom' : IsGSetHom (str A) f (gsetstr (action _*'_ SB' unit' comp'))
        hom' = record { pres* = λ g x →
             f (g * x) ≡⟨ cong (λ y → f (g * y)) (sym (retEq e _)) ⟩
             f (g * (f⁻  (f x))) ∎
             }

        unique : ( C : Σ (⟨ G ⟩ → B → B) (λ _*_ →
                                         Σ (isSet B) (λ SB →
                                           Σ ((x : B) → (str G).GroupStr.1g * x ≡ x) (λ unit →
                                             Σ ((g1 g2 : ⟨ G ⟩) (x : B) → g1 * (g2 * x) ≡ ((str G).GroupStr._·_ g1 g2) * x) (λ comp →
                                               IsGSetHom (str A) (equivFun e) (gsetstr (action _*_ SB unit comp))))))
                                               ) → (_*'_ , SB' , unit' , comp' , hom') ≡ C
        unique (_*''_ , SB'' , unit'' , comp'' , hom'') = ΣPathP (funExt (λ g → funExt λ x → *'≡*'' g x) , ΣPathP (isPropIsSet _ _ , ΣPathP (funExt (λ _ → toPathP (SB' _ _ _ _)) , ΣPathP ((funExt (λ _ → funExt λ _ → funExt λ _ → toPathP (SB' _ _ _ _))) , toPathP (equalIsGSetHom _ hom'' (funExt λ _ → funExt λ _ → toPathP (SB' _ _ _ _)))))))
          where
          *'≡*'' : (g : ⟨ G ⟩) (x : B) → g *' x ≡ g *'' x
          *'≡*'' g x =
            f (g * (f⁻ x)) ≡⟨ (hom'' .IsGSetHom.pres*) _ _ ⟩
            g *'' (f (f⁻ x)) ≡⟨ cong (λ y → g *'' y) (secEq e _) ⟩
            g *'' x ∎

GSetPath'Fst : {G : Group ℓ} {X Y : GSet G} (p : X ≡ Y) → equivFun GSetPath' p .fst ≡ pathToEquiv (cong fst p)
GSetPath'Fst {X = X} = idToGSetEquivFst

-- variant of the above where the equivalence is definitionally idToGSetEquiv
GSetPath : {G : Group ℓ} {X Y : GSet G} → (X ≡ Y) ≃ (GSetEquiv X Y)
GSetPath {G = G} {X = X} {Y = Y} = idToGSetEquiv , idToGSetEquivIsEquiv
  where
  eq : equivFun GSetPath' ≡ idToGSetEquiv
  eq = funExt λ p → Σ≡Prop (λ _ → isPropIsGSetHom) (GSetPath'Fst p ∙ sym (idToGSetEquivFst p))
  abstract
    idToGSetEquivIsEquiv : isEquiv (idToGSetEquiv {X = X} {Y = Y})
    idToGSetEquivIsEquiv = subst isEquiv eq (snd GSetPath')

-- univalence for GSets
GSetUA : {G : Group ℓ} {X Y : GSet G} → GSetEquiv X Y → X ≡ Y
GSetUA = invEq GSetPath

-- univalence for GSets extends the one on types
GSetUAFst : {G : Group ℓ} {X Y : GSet G} (f : GSetEquiv X Y) → cong fst (GSetUA f) ≡ ua (fst f)
GSetUAFst {G = G} {X = X} {Y = Y} f = isoFunInjective univalenceIso (cong fst (GSetUA f)) (ua (fst f)) lem
  where
  lem : pathToEquiv (cong fst (GSetUA f)) ≡ pathToEquiv (ua (fst f))
  lem =
    pathToEquiv (cong fst (GSetUA f)) ≡⟨ sym (idToGSetEquivFst (GSetUA f)) ⟩
    fst (idToGSetEquiv (GSetUA f))    ≡⟨ cong fst (secEq GSetPath f) ⟩
    fst f                             ≡⟨ sym (secEq univalence (fst f)) ⟩
    pathToEquiv (ua (fst f))          ∎

isGroupoidGSet : (G : Group ℓ) → isGroupoid (GSet G)
isGroupoidGSet G X Y = isOfHLevelRespectEquiv 2 (invEquiv GSetPath) (isSetΣ (isOfHLevel≃ 2 ((str X) .GSetStr.is-set) ((str Y) .GSetStr.is-set)) λ _ → isOfHLevelSuc 1 isPropIsGSetHom)
