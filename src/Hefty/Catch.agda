module Hefty.Catch where

open import Level
open import Function
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ zero zero
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)

open import Free hiding (_>>=_)
open import Free.Throw
open import Hefty hiding (_>>=_)

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
Automatable elaboration
-}

instance
  eCatch′ : ⦃ u : Universe ⦄ → ⦃ w : ε ∼ Throw ▸ ε′ ⦄ →  Elab (Catch ⦃ u ⦄) ε
  orate eCatch′ = eCatch

