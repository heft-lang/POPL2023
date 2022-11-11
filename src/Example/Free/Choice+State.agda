{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Free.Choice+State where

open import Function
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

open import Free
open import Free.Choice
open import Free.State ℕ
open import Free.Nil

open import Example.Free.State

example₁ : Free (Choice ⊕ State ⊕ Nil) ℕ
example₁ = do
  ‵put 1
  b ← ‵or
  if b then ‵incr else (do ‵incr; ‵incr)
  ‵get

test₁ : un ((given hChoice handle (flip (given hSt handle_) 0 example₁)) tt) ≡ 2 ∷ 3 ∷ []
test₁ = refl

test₁′ : un (flip (given hSt handle_) 0 ((given hChoice handle example₁) tt)) ≡ 2 ∷ 4 ∷ []
test₁′ = refl
