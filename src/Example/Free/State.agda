module Example.Free.State where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Free
open import Free.Nil
open import Free.State ℕ

‵incr : ⦃ ε ∼ State ▸ ε′ ⦄ → Free ε ℕ
‵incr = do n ← ‵get; ‵put (n + 1); ‵get

incr-test : end (handle hSt ‵incr 0) ≡ 1
incr-test = refl

incr-test₁ : end (handle hSt₁ ‵incr 0) ≡ (1 , 1)
incr-test₁ = refl
