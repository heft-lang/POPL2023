module Hefty.Lambda where

open import Function hiding (_↣_)
open import Level using (zero)
open import Data.Empty
open import Data.Unit
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ zero zero
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)

open import Free hiding (_>>=_; _>>_)
open import Free.Nil

open import Hefty hiding (_>>=_; _>>_)


{-
An interface of a universe of types with CBPV inspired function- and thunk types.
-}
record LamUniverse : Set₁ where
  field ⦃ u ⦄ : Universe
        _↣_   : Ty → Ty → Ty
        c     : Ty → Ty

open LamUniverse ⦃ ... ⦄ public


{-
Operations
-}

data LamOp ⦃ l : LamUniverse ⦄ : Set where
  lam : {t₁ t₂ : Ty}                   → LamOp
  var : {t : Ty}      → ⟦ c t ⟧        → LamOp
  app : {t₁ t₂ : Ty}  → ⟦ c t₁ ↣ t₂ ⟧  → LamOp



{-
Effect signature
-}

Lam : ⦃ l : LamUniverse ⦄ → Effectᴴ
Opᴴ    Lam              = LamOp
Forkᴴ  Lam (lam {t₁} {t₂})     = record { Op = ⟦ c t₁ ⟧; Ret = λ _ → ⟦ t₂ ⟧ }
Retᴴ   Lam (lam {t₁} {t₂})     = ⟦ c t₁ ↣ t₂ ⟧
Forkᴴ  Lam (var x)             = Nil
Retᴴ   Lam (var {t} x)         = ⟦ t ⟧
Forkᴴ  Lam (app {t₁} {t₂} fun) = record { Op = ⊤; Ret = λ _ → ⟦ t₁ ⟧ }
Retᴴ   Lam (app {t₁} {t₂} fun) = ⟦ t₂ ⟧


{-
Smart constructors
-}

module _ ⦃ l : LamUniverse ⦄ ⦃ w : H ∼ Lam ▹ H′ ⦄ where

  ‵lam  :  {t₁ t₂ : Ty}  → (⟦ c t₁ ⟧ → Hefty H ⟦ t₂ ⟧)     → Hefty H ⟦ c t₁ ↣ t₂ ⟧
  ‵lam {t₁} {t₂} b = impure (inj▹ₗ (lam {t₁} {t₂})) (proj-fork▹ₗ b) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)
  
  ‵var  :  {t : Ty}      → ⟦ c t ⟧                         → Hefty H ⟦ t ⟧
  ‵var x = impure (inj▹ₗ (var x)) (proj-fork▹ₗ (λ b → ⊥-elim b)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)
  
  ‵app  :  {t₁ t₂ : Ty}  → ⟦ c t₁ ↣ t₂ ⟧ → Hefty H ⟦ t₁ ⟧  → Hefty H ⟦ t₂ ⟧
  ‵app f m = impure (inj▹ₗ (app f)) (proj-fork▹ₗ (λ _ → m)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


{-
Elaboration 1: call-by-value interpretation
-}

module _ ⦃ l : LamUniverse ⦄
         ⦃ iso₁ : {t₁ t₂ : Ty}
                → ⟦ t₁ ↣ t₂ ⟧ ↔ (⟦ t₁ ⟧ → Free Δ ⟦ t₂ ⟧) ⦄
         ⦃ iso₂ : {t : Ty}
                → ⟦ c t ⟧ ↔ ⟦ t ⟧  ⦄ where

  open import Free using (_>>=_)
  open Inverse ⦃ ... ⦄

  eLamCBV : Elaboration Lam Δ
  alg eLamCBV lam      ψ k = k (from ψ)
  alg eLamCBV (var x)  _ k = k (to x)
  alg eLamCBV (app f)  ψ k = do
    a ← ψ tt
    v ← to f (from a)
    k v

  instance
    eLamCBV′ : Elab Lam Δ
    orate eLamCBV′ = eLamCBV


{-
Elaboration 2: call-by-name interpretation
-}

module _ ⦃ u : LamUniverse ⦄
         ⦃ iso₁ : {t₁ t₂ : Ty}
                → ⟦ t₁ ↣ t₂ ⟧ ↔ (⟦ t₁ ⟧ → Free Δ ⟦ t₂ ⟧)  ⦄
         ⦃ iso₂ : {t : Ty}
                → ⟦ c t ⟧ ↔ Free Δ ⟦ t ⟧ ⦄ where

  open import Free using (_>>=_) 
  open import Data.Nat using (ℕ)
  open Inverse ⦃ ... ⦄

  eLamCBN : Elaboration Lam Δ
  alg eLamCBN lam      ψ  k = k (from ψ)
  alg eLamCBN (var x)  _  k = to x >>= k
  alg eLamCBN (app f)  ψ  k = to f (from (ψ tt)) >>= k


  instance
    eLamCBN′ : Elab Lam Δ
    orate eLamCBN′ = eLamCBN
