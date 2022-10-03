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

‵put : ⦃ ε ∼ State ▸ ε′ ⦄ → S → Free ε ⊤
‵put ⦃ w ⦄ n = impure (inj▸ₗ (put n)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

‵get : ⦃ ε ∼ State ▸ ε′ ⦄ → Free ε S
‵get ⦃ w ⦄ = impure (inj▸ₗ get) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler:
-}

hSt : ParameterizedHandler State S id
ret hSt x _ = x
hdl hSt (put s) k s₀ = k tt s
hdl hSt get     k s  = k s  s


{-
Handler that gives access to the final state:
-}

hSt₁ : ParameterizedHandler State S (_× S)
ret hSt₁ = _,_
hdl hSt₁ (put s)  k s₀ = k tt s
hdl hSt₁ get      k s  = k s  s
