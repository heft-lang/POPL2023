{-
A state effect module, parameterized by a type of stateful data.
-}
module Free.State (S : Set) where

open import Function
open import Data.Unit
open import Data.Product
open import Data.Nat

open import Free


{-
The state effect has two operations: `put s` and `get`.
-}

data StateOp : Set where
  put : S → StateOp
  get :     StateOp


{-
The signature of the state of effect:
-}

State : Effect
Op   State         = StateOp
Ret  State (put s) = ⊤
Ret  State get     = S


{-
Smart constructors:
-}

‵put : ⦃ Δ ∼ State ▸ Δ′ ⦄ → S → Free Δ ⊤
‵put ⦃ w ⦄ n = impure (inj▸ₗ (put n)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

‵get : ⦃ Δ ∼ State ▸ Δ′ ⦄ → Free Δ S
‵get ⦃ w ⦄ = impure (inj▸ₗ get) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler:
-}

hSt : ⟨ A ! State ⇒ S ⇒ A ! Δ′ ⟩
ret hSt x _ = pure x
hdl hSt (put s) k s₀ = k tt s
hdl hSt get     k s  = k s  s


{-
Handler that gives access to the final state:
-}

hSt₁ : ⟨ A ! State ⇒ S ⇒ (A × S) ! Δ′ ⟩
ret hSt₁ x s = pure (x , s)
hdl hSt₁ (put s)  k s₀ = k tt s
hdl hSt₁ get      k s  = k s  s
