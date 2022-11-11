module Hefty.Concur where

open import Function
open import Level renaming (zero to ℓ0) using ()
open import Data.Unit
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)

open import Free hiding (_>>=_; _>>_)
open import Free.SubJump
open import Free.Interleave

open import Hefty hiding (_>>=_; _>>_)

{-
Operations
-}

data ConcurOp ⦃ u : Universe ⦄ : Set where
  spawn   : (t : Ty) → ConcurOp
  atomic  : (t : Ty) → ConcurOp


{-
Effect signature
-}

Concur : ⦃ u : Universe ⦄ → Effectᴴ
Opᴴ   Concur    = ConcurOp
Forkᴴ Concur (spawn t)  = record { Op = Bool; Ret = λ _ → ⟦ t ⟧ }
Retᴴ  Concur (spawn t)  = ⟦ t ⟧
Forkᴴ Concur (atomic t) = record { Op = ⊤; Ret = λ _ → ⟦ t ⟧ }
Retᴴ  Concur (atomic t) = ⟦ t ⟧


{-
Smart constructors
-}

module _ ⦃ u : Universe ⦄ where

  ‵spawn : ⦃ w : H ∼ Concur ▹ H′ ⦄ {t : Ty}
         → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧
  ‵spawn ⦃ w = w ⦄ {t} m₁ m₂ =
    impure (inj▹ₗ (spawn t)) (proj-fork▹ₗ (λ b → if b then m₁ else m₂)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)

  ‵atomic : ⦃ w : H ∼ Concur ▹ H′ ⦄ {t : Ty}
           → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧
  ‵atomic ⦃ w = w ⦄ {t} m = impure (inj▹ₗ (atomic t)) (proj-fork▹ₗ (λ _ → m)) (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


  {-
  Elaboration
  -}

  eConcur : {Ref : Ty → Set} ⦃ wₐ : Δ ∼ CC Ref ▸ Δ″ ⦄ → Elaboration Concur Δ
  alg eConcur (spawn t)   ψ k  =
    from-front (interleaveₗ (to-front (ψ true)) (to-front (ψ false))) >>= k
    where open import Free using (_>>=_)
  alg eConcur (atomic t)  ψ k  = ‵sub (λ ref → ψ tt >>= ‵jump ref) k
    where open import Free using (_>>=_; _>>_)

  instance
    eConcur′ : {Ref : Ty → Set} ⦃ wₐ : Δ ∼ CC Ref ▸ Δ″ ⦄ → Elab Concur Δ
    orate eConcur′ = eConcur
