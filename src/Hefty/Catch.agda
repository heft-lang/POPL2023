module Hefty.Catch where

open import Level using (zero)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ zero zero
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)

open import Free hiding (_>>=_)
open import Free.Throw
open import Free.SubJump

open import Hefty hiding (_>>=_)
open import Hefty.Lift

open Inverse ⦃ ... ⦄

{-
Operations
-}

data CatchOp (T : Set) : Set where
  catch : T → CatchOp T


{-
Effect signature
-}

Catch : ⦃ u : Universe ⦄ → Effectᴴ
Opᴴ     Catch = CatchOp Ty
Forkᴴ   Catch (catch t)  = record
  { Op = Bool; Ret = λ _ → ⟦ t ⟧ }
Retᴴ    Catch (catch t)  = ⟦ t ⟧


{-
Smart constructor
-}

‵catch   : ⦃ u : Universe ⦄ ⦃ w : H ∼ Catch ▹ H′ ⦄ {t : Ty} 
         → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧  → Hefty H ⟦ t ⟧
‵catch ⦃ w = w ⦄ m₁ m₂  =
  impure
    (inj▹ₗ (catch _))
    (proj-fork▹ₗ (λ b → if b then m₁ else m₂))
    (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


{-
A (modular) elaboration
-}

eCatch : ⦃ u : Universe ⦄ ⦃ w : Δ ∼ Throw ▸ Δ′ ⦄ →  Elaboration Catch Δ
alg eCatch (catch t) ψ k = let m₁ = ψ true; m₂ = ψ false in
  (♯ ((given hThrow handle m₁) tt)) >>= maybe k (m₂ >>= k)
  where open import Free using (_>>=_)


{-
A smarter constructor for ↑ throw
-}

‵throwᴴ : ⦃ w : H  ∼  Lift Throw  ▹ H″ ⦄
         → Hefty H A
‵throwᴴ ⦃ w ⦄ = (↑ throw) >>= ⊥-elim
  where open import Hefty using (_>>=_)


{-
A (modular) alternative elaboration that supports a transactional state
semantics of exception handling
-}

module _ ⦃ u : Universe ⦄
         {Ref : Ty → Set}
         {unit : Ty}
         ⦃ iso : ⟦ unit ⟧ ↔ ⊤ ⦄
         ⦃ w₁ : Δ ∼ CC Ref ▸ Δ′ ⦄
         ⦃ w₂ : Δ ∼ Throw ▸ Δ″ ⦄ where

  eCatchCC : Elaboration Catch Δ
  alg eCatchCC (catch x) ψ k = let m₁ = ψ true; m₂ = ψ false in
    ‵sub
      (λ r → (♯ ((given hThrow handle m₁) tt)) >>= maybe k (‵jump r (from tt)))
      (λ _ → m₂ >>= k)
    where open import Free using (_>>=_)
