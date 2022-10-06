module Free.Out where

open import Function
open import Data.Unit
open import Data.Product
open import Data.List

open import Free


{-
Operation
-}

data OutOp X : Set where
  out : X → OutOp X


{-
Effect signature
-}

Out : Set → Effect
Op (Out X) = OutOp X
Ret (Out X) (out _) = ⊤


{-
Smart constructor
-}

‵out : ⦃ ε ∼ Out X ▸ ε′ ⦄ → X → Free ε ⊤
‵out ⦃ w ⦄ x = impure (inj▸ₗ (out x)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler
-}

hOut : SimpleHandler (Out X) (_× List X)
ret  hOut x          = x , []
hdl  hOut (out x) k  = do (v , xs) ← k tt; pure (v , x ∷ xs)
