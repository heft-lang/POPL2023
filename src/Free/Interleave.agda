{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Free.Interleave where

open import Level renaming (zero to ℓ0) using ()
open import Data.Sum
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)

open import Free
open import Free.SubJump


{-
Fairly interleave two computations into one, treating operations in the first
continuation of a `sub` operation as atomic.
-}

interleaveₗ : ⦃ u : Universe ⦄ {Ref : T → Set} {-⦃ w : ε ∼ Choice ▸ ε′ ⦄-}
            → Free (CC Ref ⊕ ε) A → Free (CC Ref ⊕ ε) B → Free (CC Ref ⊕ ε) A
interleaveₗ (pure x) (pure _) = pure x
interleaveₗ (pure x) m₂ = fmap (λ _ → x) m₂
interleaveₗ m₁ (pure x) = m₁
interleaveₗ (impure (inj₁ (jump ref x)) _) m₂ = do
  m₂
  ‵jump ref x
interleaveₗ m₁ (impure (inj₁ (jump ref x)) _) = do
  m₁
  ‵jump ref x
interleaveₗ (impure (inj₁ sub) k₁) (impure (inj₁ sub) k₂) =
  impure
    (inj₁ sub)
    (λ{ (inj₁ x) → k₁ (inj₁ x)
      ; (inj₂ y) →
        impure
          (inj₁ sub)
          (λ{ (inj₁ x) → k₂ (inj₁ x) >>= λ _ → k₁ (inj₂ y)
            ; (inj₂ z) → interleaveₗ (k₁ (inj₂ y)) (k₂ (inj₂ z)) }) })
interleaveₗ (impure (inj₁ sub) k₁) (impure (inj₂ op₂) k₂) = do
  impure
    (inj₁ sub)
    (λ{ (inj₁ x) → k₁ (inj₁ x)
      ; (inj₂ y) →
        impure
          (inj₂ op₂)
          (λ z → interleaveₗ (k₁ (inj₂ y)) (k₂ z)) })
interleaveₗ (impure (inj₂ op₁) k₁) (impure (inj₁ sub) k₂) =
  impure
    (inj₂ op₁)
    (λ x →
      impure
        (inj₁ sub)
        (λ{ (inj₁ y) → k₂ (inj₁ y) >>= λ _ → k₁ x
          ; (inj₂ z) → interleaveₗ (k₁ x) (k₂ (inj₂ z)) }))
interleaveₗ (impure (inj₂ op₁) k₁) (impure (inj₂ op₂) k₂) =
  impure (inj₂ op₁) (λ x₁ → impure (inj₂ op₂) (λ x₂ → interleaveₗ (k₁ x₁) (k₂ x₂)))

