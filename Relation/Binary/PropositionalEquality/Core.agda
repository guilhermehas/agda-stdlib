------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.PropositionalEquality.

module Relation.Binary.PropositionalEquality.Core where

open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.Consequences.Core

------------------------------------------------------------------------
-- Some properties

≡-sym : {a : Set} -> Symmetric {a} _≡_
≡-sym ≡-refl = ≡-refl

≡-trans : {a : Set} -> Transitive {a} _≡_
≡-trans ≡-refl ≡-refl = ≡-refl

≡-subst : {a : Set} -> Substitutive {a} _≡_
≡-subst P ≡-refl p = p

≡-resp : forall {a} (∼ : Rel a) -> _≡_ Respects₂ ∼
≡-resp _∼_ = subst⟶resp₂ _∼_ ≡-subst

≡-isEquivalence : forall {a} -> IsEquivalence {a} _≡_
≡-isEquivalence = record
  { refl  = ≡-refl
  ; sym   = ≡-sym
  ; trans = ≡-trans
  }
