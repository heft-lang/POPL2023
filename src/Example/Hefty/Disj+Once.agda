{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Hefty.Disj+Once where

open import Level renaming (zero to ℓ0) using ()
open import Data.Unit
open import Data.Nat
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; head)
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)
open import Relation.Binary.PropositionalEquality

open import Free hiding (_>>=_; _>>_)
open import Free.Disj
open import Free.Nil

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Once
open import Hefty.Lift
open import Hefty.Nil


{-
A universe of types
-}

data Type : Set where
  num   : Type
  unit  : Type

private instance
  OnceUniverse : Universe
  T ⦃ OnceUniverse ⦄ = Type
  ⟦_⟧ ⦃ OnceUniverse ⦄ num = ℕ
  ⟦_⟧ ⦃ OnceUniverse ⦄ unit = ⊤


{-
Example programs
-}

ex-0or1 : Hefty (Lift Disj ∔ Once ∔ Lift Nil) ℕ
ex-0or1 = (pure 0) ‵orᴴ (pure 1)

ex-fail-once : Hefty (Lift Disj ∔ Once ∔ Lift Nil) ℕ
ex-fail-once = do
  r ← ‵once ex-0or1
  if r ≡ᵇ 0 then ‵failᴴ else pure r
  where open import Hefty using (_>>=_)


{-
Automatic elaboration
-}

once-elab : Elab (Lift Disj ∔ Once ∔ Lift Nil) (Disj ⊕ Nil)
once-elab = auto-elab


{-
Tests
-}

test-ex-0or1 : end (handle₀ hDisj (elab once-elab ex-0or1)) ≡ 0 ∷ 1 ∷ []
test-ex-0or1 = refl

test-fail-once : end (handle₀ hDisj (elab once-elab ex-fail-once)) ≡ []
test-fail-once = refl
