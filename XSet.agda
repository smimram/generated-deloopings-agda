{-

  This file contains:

  - Definition of Set Actions
  - Definition of XSets and the XSet Structure

-}

{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Group
open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ : Level

-- Action of a set on a set
record SetAction (X : hSet ℓ) (A : Type ℓ) : Type ℓ where
  constructor
    action
  field
    _*_ : ⟨ X ⟩ → A → A
    is-set : isSet A

unquoteDecl SetActionIsoΣ = declareRecordIsoΣ SetActionIsoΣ (quote SetAction)

record XSetStr (X : hSet ℓ) (A : Type ℓ) : Type ℓ where
  constructor
    xsetstr
  field
    ϕ : SetAction {ℓ} X A

  open SetAction ϕ public

unquoteDecl XSetStrIsoΣ = declareRecordIsoΣ XSetStrIsoΣ (quote XSetStr)

-- X-sets are sets together with an action of X
XSet : {ℓ : Level} → hSet ℓ → Type (ℓ-suc ℓ)
XSet {ℓ} X = TypeWithStr ℓ (XSetStr X)
