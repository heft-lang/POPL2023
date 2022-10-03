{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Free.Choice+State where

open import Function
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
  b ← ‵choose
  if b then ‵incr else (do ‵incr; ‵incr)
  ‵get

test₁ : end (handle₀ hChoice (flip (handle hSt) 0 example₁)) ≡ 2 ∷ 3 ∷ []
test₁ = refl

test₁′ : end (flip (handle hSt) 0 (handle₀ hChoice example₁)) ≡ 2 ∷ 4 ∷ []
test₁′ = refl
