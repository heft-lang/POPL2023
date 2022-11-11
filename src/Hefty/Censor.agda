module Hefty.Censor where

open import Level using (zero)
open import Function
open import Data.Unit
open import Data.Product
open import Data.String
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ zero zero
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)

open import Hefty hiding (_>>=_; _>>_)
open import Free hiding (_>>=_; _>>_)
open import Free.Output


{-
Operation
-}

data CensorOp (T : Set) : Set where
  censor : (String → String) → T → CensorOp T


{-
Effect signature
-}

Censor : ⦃ u : Universe ⦄ → Effectᴴ
Opᴴ   Censor = CensorOp Ty
Forkᴴ Censor (censor f t) = record { Op = ⊤ ; Ret = λ _ → ⟦ t ⟧ }
Retᴴ  Censor (censor f t) = ⟦ t ⟧


{-
Smart constructor
-}

‵censor : ⦃ u : Universe ⦄ ⦃ w : H ∼ Censor ▹ H′ ⦄ {t : Ty}
        → (String → String) → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧
‵censor ⦃ w = w ⦄ f m = impure
  (inj▹ₗ (censor f _))
  (proj-fork▹ₗ (λ _ → m))
  (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


{-
A (modular) elaboration
-}

eCensor : ⦃ u : Universe ⦄ ⦃ w : Δ ∼ Output ▸ Δ′ ⦄ → Elaboration Censor Δ
alg eCensor (censor f t) ψ k = do
  (x , s) ← (♯ (given hOut handle (ψ tt)) tt)
  ‵out (f s)
  k x
  where open import Free using (_>>=_; _>>_)

{-
Alternative elaboration that atomically censors
-}

eCensor′ : ⦃ u : Universe ⦄ ⦃ w : Δ ∼ Output ▸ Δ′ ⦄ → Elaboration Censor Δ
alg eCensor′ (censor f t) ψ k = do
  (x , s) ← (♯ (given (hOut′ f) handle (ψ tt)) tt)
  ‵out s
  k x
  where open import Free using (_>>=_; _>>_)

