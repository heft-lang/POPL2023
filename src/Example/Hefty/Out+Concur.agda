{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Hefty.Out+Concur where

open import Level renaming (zero to ℓ0) using ()
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.String
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)
open import Relation.Binary.PropositionalEquality

open import Free  hiding (_>>=_; _>>_)
open import Free.Out
open import Free.SubJump
open import Free.Nil

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Lift
open import Hefty.Concur
open import Hefty.Nil


{-
A simple universe of types
-}

data Type : Set where
  unit : Type
  num : Type

instance
  ConcurUniverse : Universe
  Ty ⦃ ConcurUniverse ⦄ = Type
  ⟦_⟧ ⦃ ConcurUniverse ⦄ unit = ⊤
  ⟦_⟧ ⦃ ConcurUniverse ⦄ num = ℕ


{-
Automatic elaboration
-}

concur-elab : Elab (Lift Output ∔ Concur ∔ Lift Nil)
                   (  CC (λ t → ⟦ t ⟧ → Free (Output ⊕ Nil) ℕ)
                   ⊕ Output
                   ⊕ Nil )
concur-elab = auto-elab


{-
Tests
-}

ex-01234 : Hefty (Lift Output ∔ Concur ∔ Lift Nil) ℕ
ex-01234 = ‵spawn (do ↑ out "0"; ↑ out "1"; ↑ out "2"; pure 0)
                  (do ↑ out "3"; ↑ out "4"; pure 0)
           where open import Hefty using (_>>_)

test-ex-01234 :  un (  (  given hOut
                          handle (  (  given hCC
                                       handle (elab concur-elab ex-01234)
                                    ) tt ) ) tt ) ≡ (0 , "03142")
test-ex-01234 = refl


ex-01234567 : Hefty (Lift Output ∔ Concur ∔ Lift Nil) ℕ
ex-01234567 = ‵spawn  ex-01234
                      (‵atomic (do ↑ out "5"; ↑ out "6"; ↑ out "7"; pure 0))
              where open import Hefty using (_>>_)

test-ex-01234567 :  un (  (  given hOut
                             handle (  (  given hCC
                                          handle (elab concur-elab ex-01234567)
                                       ) tt ) ) tt ) ≡ (0 , "05673142")
test-ex-01234567 = refl


{-
Alternative ordering of effects
-}

concur-elab′ : Elab (Lift Output ∔ Concur ∔ Lift Nil)
                   (  Output
                   ⊕ CC (λ t → ⟦ t ⟧ → Free Nil (ℕ × String))
                   ⊕ Nil )
concur-elab′ = auto-elab

test-ex′ : un (  (  given hCC
                    handle (  (  given hOut
                                 handle (elab concur-elab′ ex-01234) )
                              tt ) ) tt ) ≡ (0 , "03142")
test-ex′ = refl

ex-atomic-01234 : Hefty (Lift Output ∔ Concur ∔ Lift Nil) ℕ
ex-atomic-01234 = ‵spawn (‵atomic (do ↑ out "0"; ↑ out "1"; ↑ out "2"; pure 0)) (do ↑ out "3"; ↑ out "4"; pure 0)
  where open import Hefty using (_>>_)

test-atomic-ex : un ((given hCC handle ((given hOut handle (elab concur-elab′ ex-atomic-01234)) tt)) tt) ≡ (0 , "34")
test-atomic-ex = refl
