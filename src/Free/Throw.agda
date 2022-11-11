module Free.Throw where

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Maybe

open import Free


{-
A throw operation.
-}

data ThrowOp : Set where
  throw : ThrowOp


{-
A throw effect.
-}

Throw : Effect
Op  Throw = ThrowOp
Ret Throw throw = ⊥


{-
Smart constructor.
-}

‵throw : ⦃ Δ ∼ Throw ▸ Δ′ ⦄ → Free Δ A
‵throw ⦃ w ⦄ = impure (inj▸ₗ throw) (⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler
-}

hThrow : ⟨ A ! Throw ⇒ ⊤ ⇒ (Maybe A) ! Δ′ ⟩
ret  hThrow x _       = pure (just x)
hdl  hThrow throw k _ = pure nothing
