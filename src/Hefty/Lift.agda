module Hefty.Lift where

open import Function
open import Data.Empty

open import Free
open import Hefty
open import Free.Nil

{-
Lifting an algebraic effect to a higher-order effect
-}

Lift : Effect → Effectᴴ
Opᴴ     (Lift Δ)    = Op Δ
Forkᴴ   (Lift Δ) _  = Nil
Retᴴ    (Lift Δ)    = Ret Δ


{-
Smart constructor
-}

↑_ : ⦃ w : H ∼ Lift Δ ▹ H′ ⦄ → (op : Op Δ) → Hefty H (Ret Δ op)
↑_ ⦃ w ⦄ op =
  impure (inj▹ₗ ⦃ w ⦄ op) (proj-fork▹ₗ ⦃ w ⦄ (λ b → ⊥-elim b)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


{-
A (modular) elaboration
-}

eLift : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → Elaboration (Lift Δ₀) Δ
alg (eLift ⦃ w ⦄) op ψ k = impure (inj▸ₗ op) (k ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Automatable elaboration
-}

instance
  eLift′ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → Elab (Lift Δ₀) Δ
  orate eLift′ = eLift

