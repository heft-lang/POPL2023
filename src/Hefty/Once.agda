module Hefty.Once where

open import Function
open import Level renaming (zero to ℓ0) using ()
open import Data.Empty
open import Data.Unit
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; _∷_; []; head)
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)

open import Free hiding (_>>=_; _>>_)
open import Free.Disj

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Lift


{-
Operation
-}

data OnceOp ⦃ u : Universe ⦄ : Set where
  once : {t : T} → OnceOp


{-
Effect signature
-}

Once : ⦃ u : Universe ⦄ → Effectᴴ
Op    Once          = OnceOp
Fork  Once (once {t}) = record
  { Op = ⊤; Ret = λ _ →  ⟦ t ⟧ }
Ret   Once (once {t}) = ⟦ t ⟧


{-
Smart constructors
-}

_‵orᴴ_  : ⦃ H ∼ Lift Disj ▹ H′ ⦄ → Hefty H A → Hefty H A  → Hefty H A
_‵orᴴ_ ⦃ w ⦄ m₁ m₂ = (↑ or) >>= (if_then m₁ else m₂)
  where open import Hefty using (_>>=_)

‵failᴴ  : ⦃ H ∼ Lift Disj ▹ H′ ⦄                          → Hefty H A
‵failᴴ ⦃ w ⦄ = (↑ fail) >>= ⊥-elim
  where open import Hefty using (_>>=_)

‵once : ⦃ u : Universe ⦄ ⦃ w : H ∼ Once ▹ H′ ⦄ {t : T} → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧
‵once ⦃ w = w ⦄ {t} b = impure (inj▹ₗ once) (proj-fork▹ₗ (λ _ → b)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


{-
Elaboration
-}

eOnce : ⦃ u : Universe ⦄ ⦃ w : ε ∼ Disj ▸ ε′ ⦄ → Elaboration Once ε
alg eOnce once ψ k = do
  l ← ♯ (handle₀ hDisj (ψ tt))
  maybe k ‵fail (head l)
  where open import Free using (_>>=_)

instance
  eOnce′ : ⦃ u : Universe ⦄ ⦃ w : ε ∼ Disj ▸ ε′ ⦄ → Elab Once ε
  orate eOnce′ = eOnce
