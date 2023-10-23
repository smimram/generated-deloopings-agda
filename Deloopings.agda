{-

  This file contains:

  - Delooping by torsors (classical construction and proof)
  - Delooping by generated torsors
  - Caracterisation of the Principal torsor's Aut group

  -}

{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.FreeGroup renaming (_·_ to _·f_)
open import Cubical.Homotopy.Group.Base

open import XSet
open import GSet
open import GSetHom
open import GSetProperties
open import Generators
open import XSetProperties
open import Comp
open import PrincipalTorsor


private
  variable
    ℓ : Level

module _ {G : Group ℓ} {X : hSet ℓ} {ι : ⟨ X ⟩ → ⟨ G ⟩} where
  open generators {G = G} {X = X} {ι = ι}
  open principal-torsor
  module _ {gen : ι-generates} where
  BG : Pointed (ℓ-suc ℓ)
  BG = Comp (GSet G , PG)

  isGroupoidBG : isGroupoid ⟨ BG ⟩
  isGroupoidBG = groupoidComp (GSet G , PG) (isGroupoidGSet G)

  PX : XSet X
  PX = U {G = G} {ι = ι} PG

  BG' : Pointed (ℓ-suc ℓ)
  BG' = Comp (XSet X , PX)

  PGloops : GroupIso (π₁ (GSet G , PG) (isGroupoidGSet G)) G
  PGloops = e , gh
    where
    open Iso
    open GroupStr (str G)
    m≃ : ⟨ G ⟩ → GSetEquiv (PG {G = G}) PG
    m≃ x = (isoToEquiv e , makeIsGSetEquiv {G = G} λ y z → sym (·Assoc _ _ _))
      where
      e : Iso ⟨ PG {G = G} ⟩ ⟨ PG {G = G} ⟩
      fun e y = y · x
      Iso.inv e y = y · GroupStr.inv (str G) x
      rightInv e y = sym (·Assoc _ _ _) ∙ cong (λ x → y · x) (·InvL x) ∙ ·IdR y
      leftInv  e y = sym (·Assoc _ _ _) ∙ cong (λ x → y · x) (·InvR x) ∙ ·IdR y
    m : ⟨ G ⟩ → PG {G = G} ≡ PG
    m x = GSetUA (m≃ x)
    f : (PG ≡ PG) → ⟨ G ⟩
    f p = transport (cong fst p) 1g
    e : Iso (PG ≡ PG) ⟨ G ⟩
    fun e = f
    Iso.inv e x = m x
    rightInv e x = mTr x 1g ∙ ·IdL x
      where
      mTr : (x y : ⟨ G ⟩) → subst fst (m x) y ≡ y · x
      mTr x y =
        subst fst (m x) y             ≡⟨ refl ⟩
        transport (cong fst (m x)) y  ≡⟨ funExt⁻ (cong transport (GSetUAFst (m≃ x))) y ⟩
        transport (ua (fst (m≃ x))) y ≡⟨ uaβ (fst (m≃ x)) y ⟩
        y · x                         ∎
    -- we are using here the variant of pathEq for GSets
    leftInv e p = isEmbedding→Inj {f = idToGSetEquiv} (isEquiv→isEmbedding GSetUnivalence) (m (subst fst p 1g)) p (GSetEquiv≡ lem)
      where
      q : ⟨ G ⟩ ≡ ⟨ G ⟩
      q = cong fst p
      qNat : (x y : ⟨ G ⟩) → x · transport q y ≡ transport q (x · y)
      qNat x y = sym (equivFun GSetPath' p .snd .IsGSetHom.pres* x y)
      lem =
        equivFun (fst (idToGSetEquiv (m (subst fst p 1g)))) ≡⟨ refl ⟩
        equivFun (fst (idToGSetEquiv (m (transport q 1g)))) ≡⟨ cong equivFun (cong fst (GSetUAβ _)) ⟩
        equivFun (fst (m≃ (transport q 1g)))                ≡⟨ refl ⟩
        (λ y → y · (transport q 1g))                        ≡⟨ funExt (λ y → qNat y 1g) ⟩
        (λ y → transport q (y · 1g))                        ≡⟨ funExt (λ y → cong (transport q) (·IdR y)) ⟩
        transport q                                         ≡⟨ refl ⟩
        equivFun (pathToEquiv q)                            ≡⟨ cong equivFun (sym (idToGSetEquivFst p)) ⟩
        equivFun (fst (idToGSetEquiv p))                    ∎
    open IsGroupHom
    gh : IsGroupHom (str (π₁ (GSet G , PG) (isGroupoidGSet G))) f (str G)
    pres· gh p q =
      f ((str (π₁ (GSet G , PG) (isGroupoidGSet G)) GroupStr.· p) q) ≡⟨ refl ⟩
      f (p ∙ q) ≡⟨ refl ⟩
      transport (cong fst (p ∙ q)) 1g ≡⟨ refl ⟩
      transport (cong fst p ∙ cong fst q) 1g ≡⟨ transportComposite (cong fst p) (cong fst q) 1g ⟩
      transport (cong fst q) (transport (cong fst p) 1g) ≡⟨ refl ⟩
      transport (cong fst q) (f p) ≡⟨ cong (transport (cong fst q)) (sym (·IdR (f p))) ⟩
      transport (cong fst q) (f p · 1g) ≡⟨ {!!} ⟩ -- naturality (generalization of qNat)
      f p · transport (cong fst q) 1g ≡⟨ refl ⟩
      f p · f q ∎
    pres1 gh =
      f (GroupStr.1g (str (π₁ (GSet G , PG) (isGroupoidGSet G)))) ≡⟨ refl ⟩
      transport (cong fst (GroupStr.1g (str (π₁ (GSet G , PG) (isGroupoidGSet G))))) 1g ≡⟨ refl ⟩
      transport (cong fst (refl {x = PG {G = G}})) 1g ≡⟨ refl ⟩
      transport (refl {x = ⟨ G ⟩}) 1g ≡⟨ transportRefl 1g ⟩
      1g ∎
    presinv gh p =
      f (GroupStr.inv (str (π₁ (GSet G , PG) (isGroupoidGSet G))) p) ≡⟨ refl ⟩
      f (sym p) ≡⟨ refl ⟩
      transport (cong fst (sym p)) 1g ≡⟨ refl ⟩
      transport (sym (cong fst p)) 1g ≡⟨ {!!} ⟩ -- inverse by naturality too
      GroupStr.inv (str G) (f p) ∎

  torsorDeloops : GroupIso (π₁ BG isGroupoidBG) G
  torsorDeloops = compGroupIso {G = π₁ BG isGroupoidBG} (π₁Comp (GSet G , PG) (isGroupoidGSet G)) PGloops
