module Free.Out where

open import Function
open import Data.Unit
open import Data.Product
open import Data.String

open import Free


{-
Operation
-}

data OutOp : Set where
  out : String → OutOp


{-
Effect signature
-}

Output : Effect
Op Output = OutOp
Ret Output (out s) = ⊤


{-
Smart constructor
-}

‵out : ⦃ Δ ∼ Output ▸ Δ′ ⦄ → String → Free Δ ⊤
‵out ⦃ w ⦄ s = impure (inj▸ₗ (out s)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler
-}

hOut : ⟨ A ! Output ⇒ P ⇒ (A × String) ! Δ′ ⟩
ret  hOut x _          = pure (x , "")
hdl  hOut (out s) k p  = do (v , s′) ← k tt p; pure (v , s ++ s′)
