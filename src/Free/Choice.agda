module Free.Choice where

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.List hiding (or)

open import Free

{- Operation -}

data ChoiceOp : Set where
  or   : ChoiceOp
  fail : ChoiceOp


{- Effect -}

Choice : Effect
Op  Choice = ChoiceOp
Ret Choice or = Bool
Ret Choice fail = ⊥


{- Smart constructor -}

‵or : ⦃ Δ ∼ Choice ▸ Δ′ ⦄ → Free Δ Bool
‵or ⦃ w ⦄ = impure (inj▸ₗ or) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)

‵fail : ⦃ Δ ∼ Choice ▸ Δ′ ⦄ → Free Δ A
‵fail ⦃ w ⦄ = impure (inj▸ₗ fail) (⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)


{- Handler -}

hChoice : ⟨ A ! Choice ⇒ ⊤ ⇒ (List A) ! Δ′ ⟩
ret hChoice x _ = pure [ x ]
hdl hChoice or k p = do
  l₁ ← k true p
  l₂ ← k false p
  pure (l₁ ++ l₂)
hdl hChoice fail k _ = pure []
