module Free.Throw where

open import Function
open import Data.Empty
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

‵throw : ⦃ ε ∼ Throw ▸ ε′ ⦄ → Free ε A
‵throw ⦃ w ⦄ = impure (inj▸ₗ throw) (⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler
-}

hThrow : SimpleHandler Throw Maybe
ret  hThrow          = just
hdl  hThrow throw k  = pure nothing
