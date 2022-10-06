{-
The sub/jump operations due to Thielecke and Fiore and Staton.

Implementation in terms of free monad is due to Schrijvers, Piróg, Wu, and Jaskelioff.
-}
module Free.SubJump where

open import Function
open import Level using (zero)
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
module _ ⦃ u : Universe ⦄ {Ref : T → Set} ⦃ w : ε ∼ CC Ref ▸ ε′ ⦄ where
  ‵sub   : {t : T} → (Ref t → Free ε A) → (⟦ t ⟧ → Free ε A)  → Free ε A
  ‵sub b k = impure
    (inj▸ₗ ⦃ w ⦄ sub)
    ([ b , k ] ∘  proj-ret▸ₗ ⦃ w ⦄)

  ‵jump  : {t : T} → Ref t → ⟦ t ⟧                            → Free ε B
  ‵jump ref x = impure
    (inj▸ₗ (jump ref x))
    (⊥-elim ∘ proj-ret▸ₗ ⦃ w ⦄)


{-
Handler
-}

hCC : ⦃ u : Universe ⦄ → ExplicitSimpleHandler (CC (λ t → ⟦ t ⟧ → Free ε′ A)) ε′ A id
ret  hCC                  = id
hdl  hCC sub           k  = let c = k ∘ inj₂ in k (inj₁ c)
hdl  hCC (jump ref x)  k  = ref x

