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
Op     (Lift ε)    = Op ε
Fork   (Lift ε) _  = Nil
Ret    (Lift ε)    = Ret ε


{-
Smart constructor
-}

↑_ : ⦃ w : H ∼ Lift ε ▹ H′ ⦄ → (op : Op ε) → Hefty H (Ret ε op)
↑_ ⦃ w ⦄ op =
  impure (inj▹ₗ ⦃ w ⦄ op) (proj-fork▹ₗ ⦃ w ⦄ (λ b → ⊥-elim b)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


{-
A (modular) elaboration
-}

eLift : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Elaboration (Lift ε₀) ε
alg (eLift ⦃ w ⦄) op ψ k = impure (inj▸ₗ op) (k ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Automatable elaboration
-}

instance
  eLift′ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Elab (Lift ε₀) ε
  orate eLift′ = eLift

