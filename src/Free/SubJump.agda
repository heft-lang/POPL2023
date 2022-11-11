{-
The sub/jump operations due to Thielecke and Fiore and Staton.

Implementation in terms of free monad is due to Schrijvers, Piróg, Wu, and Jaskelioff.
-}
module Free.SubJump where

open import Function
open import Level using (zero)
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ zero zero
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)

open import Free

{-
Operations
-}

data CCOp ⦃ u : Universe ⦄ (Ref : T → Set) : Set where
  sub   : {t : T}                           →  CCOp Ref
  jump  : {t : T} (ref : Ref t) (x : ⟦ t ⟧) →  CCOp Ref


{-
Effect signature
-}

CC : ⦃ u : Universe ⦄ (Ref : T → Set) → Effect
Op  (CC Ref) = CCOp Ref
Ret (CC Ref) (sub {t})         = Ref t ⊎ ⟦ t ⟧
Ret (CC Ref) (jump ref x)  = ⊥


{-
Smart constructors
-}
module _ ⦃ u : Universe ⦄ {Ref : T → Set} ⦃ w : Δ ∼ CC Ref ▸ Δ′ ⦄ where
  ‵sub   : {t : T} → (Ref t → Free Δ A) → (⟦ t ⟧ → Free Δ A)  → Free Δ A
  ‵sub b k = impure
    (inj▸ₗ ⦃ w ⦄ sub)
    ([ b , k ] ∘  proj-ret▸ₗ ⦃ w ⦄)

  ‵jump  : {t : T} → Ref t → ⟦ t ⟧                            → Free Δ B
  ‵jump ref x = impure
    (inj▸ₗ (jump ref x))
    (⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler
-}

hCC : ⦃ u : Universe ⦄ → ⟨ A ! (CC (λ t → ⟦ t ⟧ → Free Δ′ A)) ⇒ ⊤ ⇒ A ! Δ′ ⟩
ret  hCC x _                = pure x
hdl  hCC sub           k p  = let c = flip k p ∘ inj₂ in k (inj₁ c) p
hdl  hCC (jump ref x)  k p  = ref x

