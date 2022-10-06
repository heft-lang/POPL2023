module Hefty.Catch where

open import Level using (zero)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ zero zero
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)

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
Op     Catch = CatchOp T
Fork   Catch (catch t)  = record
  { Op = Bool; Ret = λ _ → ⟦ t ⟧ }
Ret    Catch (catch t)  = ⟦ t ⟧


{-
Smart constructor
-}

‵catch   : ⦃ u : Universe ⦄ ⦃ w : H ∼ Catch ▹ H′ ⦄ {t : T} 
         → Hefty H ⟦ t ⟧ → Hefty H ⟦ t ⟧  → Hefty H ⟦ t ⟧
‵catch ⦃ w = w ⦄ m₁ m₂  =
  impure
    (inj▹ₗ (catch _))
    (proj-fork▹ₗ (λ b → if b then m₁ else m₂))
    (pure ∘ proj-ret▹ₗ ⦃ w ⦄)


{-
A (modular) elaboration
-}

eCatch : ⦃ u : Universe ⦄ ⦃ w : ε ∼ Throw ▸ ε′ ⦄ →  Elaboration Catch ε
alg eCatch (catch t) ψ k = let m₁ = ψ true; m₂ = ψ false in
  (♯ (handle₀ hThrow m₁)) >>= maybe k (m₂ >>= k)
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
         {Ref : T → Set}
         {unit : T}
         ⦃ iso : ⟦ unit ⟧ ↔ ⊤ ⦄
         ⦃ w₁ : ε ∼ CC Ref ▸ ε′ ⦄
         ⦃ w₂ : ε ∼ Throw ▸ ε″ ⦄ where

  eCatchCC : Elaboration Catch ε
  alg eCatchCC (catch x) ψ k = let m₁ = ψ true; m₂ = ψ false in
    ‵sub
      (λ r → (♯ (handle₀ hThrow m₁)) >>= maybe k (‵jump r (from tt)))
      (λ _ → m₂ >>= k)
    where open import Free using (_>>=_)
