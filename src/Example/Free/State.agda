module Example.Free.State where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Free
open import Free.Nil
open import Free.State ℕ

‵incr : ⦃ Δ ∼ State ▸ Δ′ ⦄ → Free Δ ℕ
‵incr = do n ← ‵get; ‵put (n + 1); ‵get

incr-test : un ((given hSt handle ‵incr) 0) ≡ 1
incr-test = refl

incr-test₁ : un ((given hSt₁ handle ‵incr) 0) ≡ (1 , 1)
incr-test₁ = refl
