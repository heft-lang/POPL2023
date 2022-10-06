module Free.Disj where

open import Function
open import Data.Empty
open import Data.Bool
open import Data.List using (List; _∷_; []; _++_)

open import Free hiding (_>>=_; _>>_)


{-
Operations
-}

data DisjOp : Set where
  or    : DisjOp
  fail  : DisjOp


{-
Effect signature
-}

Disj : Effect
Op  Disj = DisjOp
Ret Disj or = Bool
Ret Disj fail = ⊥


{-
Smart constructors
-}

‵fail : ⦃ ε ∼ Disj ▸ ε′ ⦄ → Free ε A
‵fail ⦃ w ⦄ = impure (inj▸ₗ fail) (⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)

_‵or_ : ⦃ ε ∼ Disj ▸ ε′ ⦄ → Free ε A → Free ε A → Free ε A
_‵or_ ⦃ w ⦄ m₁ m₂ = impure (inj▸ₗ or) ((if_then m₁ else m₂) ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler
-}

hDisj : SimpleHandler Disj List
ret hDisj = _∷ []
hdl hDisj or   k = do
  l₁ ← k true
  l₂ ← k false
  pure (l₁ ++ l₂)
  where open import Free using (_>>=_)
hdl hDisj fail k = pure []

