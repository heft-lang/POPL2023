{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Hefty.Choice+Once where

open import Level renaming (zero to ℓ0) using ()
open import Function
open import Data.Unit
open import Data.Nat
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; head)
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)
open import Relation.Binary.PropositionalEquality

open import Free hiding (_>>=_; _>>_)
open import Free.Choice
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
  Ty ⦃ OnceUniverse ⦄ = Type
  ⟦_⟧ ⦃ OnceUniverse ⦄ num = ℕ
  ⟦_⟧ ⦃ OnceUniverse ⦄ unit = ⊤


{-
Example programs
-}

ex-0or1 : Hefty (Lift Choice ∔ Once ∔ Lift Nil) ℕ
ex-0or1 = (pure 0) ‵orᴴ (pure 1)

ex-fail-once : Hefty (Lift Choice ∔ Once ∔ Lift Nil) ℕ
ex-fail-once = do
  r ← ‵once ex-0or1
  if r ≡ᵇ 0 then ‵failᴴ else pure r
  where open import Hefty using (_>>=_)


{-
Automatic elaboration
-}

once-elab : Elab (Lift Choice ∔ Once ∔ Lift Nil) (Choice ⊕ Nil)
once-elab = auto-elab


{-
Tests
-}

test-ex-0or1 : un (given hChoice handle (elab once-elab ex-0or1) $ tt) ≡ 0 ∷ 1 ∷ []
test-ex-0or1 = refl

test-fail-once : un (given hChoice handle (elab once-elab ex-fail-once) $ tt) ≡ []
test-fail-once = refl
