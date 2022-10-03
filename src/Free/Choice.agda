module Free.Choice where

open import Function
open import Data.Bool
open import Data.List

open import Free

{- Operation -}

data ChoiceOp : Set where
  choose : ChoiceOp


{- Effect -}

Choice : Effect
Op  Choice = ChoiceOp
Ret Choice choose = Bool


{- Smart constructor -}

‵choose : ⦃ ε ∼ Choice ▸ ε′ ⦄ → Free ε Bool
‵choose ⦃ w ⦄ = impure (inj▸ₗ choose) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)


{- Handler -}

hChoice : SimpleHandler Choice List
ret hChoice = [_]
hdl hChoice choose k = do
  l₁ ← k true
  l₂ ← k false
  pure (l₁ ++ l₂)
