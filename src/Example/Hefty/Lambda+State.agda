{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Hefty.Lambda+State where

open import Function hiding (_↣_; _⟶_)
open import Level renaming (zero to ℓ0) using ()
open import Data.Nat
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)
open import Relation.Binary.PropositionalEquality

open import Free hiding (_>>=_; _>>_)
open import Free.State ℕ
open import Free.Nil

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Lift
open import Hefty.Lambda
open import Hefty.Nil

open import Function.Construct.Identity using (↔-id)


{-
A universe of types polymorphic test program
-}

module _ ⦃ u : LamUniverse ⦄ {num : Ty}
         ⦃ iso₁ : ⟦ num ⟧ ↔ ℕ ⦄ where

  open import Hefty using (_>>=_; _>>_)
  open Inverse ⦃ ... ⦄

  ex : Hefty (Lam ∔ Lift State ∔ Lift Nil) ℕ
  ex = do
    ↑ put 1
    f ← ‵lam (λ x → do
          n₁ ← ‵var x
          n₂ ← ‵var x
          pure (from ((to n₁) + (to n₂))))
    v ← ‵app f incr
    pure (to v)
    where incr = do s₀ ← ↑ get; ↑ put (s₀ + 1); s₁ ← ↑ get; pure (from s₁)

{-
A call-by-value interpretation of the universe of types
-}

module CBVInterpretation where

  {-
  A universe of types with functions and numbers
  -}

  data Type : Set where
    _⟶_ : (t₁ t₂ : Type) → Type
    num : Type

  private instance
    CBVUniverse : Universe
    Ty ⦃ CBVUniverse ⦄ = Type
    ⟦_⟧ ⦃ CBVUniverse ⦄ (t ⟶ t₁)  = ⟦ t ⟧ → Free (State ⊕ Nil) ⟦ t₁ ⟧
    ⟦_⟧ ⦃ CBVUniverse ⦄ num       = ℕ


    {-
    The call-by-value interpretation adheres to the LamUniverse interface from
    `Hefty.Lambda`
    -}

    iso-num : ℕ ↔ ⟦ num ⟧
    iso-num = ↔-id _

    iso-fun : {t₁ t₂ : Type}
            → (⟦ t₁ ⟧ → Free (State ⊕ Nil) ⟦ t₂ ⟧) ↔ ⟦ t₁ ⟶ t₂ ⟧
    iso-fun = ↔-id _

    iso-c : {t : Type} → ⟦ t ⟧ ↔ ⟦ id t ⟧
    iso-c = ↔-id _

    LamCBVUniverse : LamUniverse
    u    ⦃ LamCBVUniverse ⦄ = CBVUniverse
    _↣_  ⦃ LamCBVUniverse ⦄ = _⟶_
    c    ⦃ LamCBVUniverse ⦄ = id


  {-
  Automatic elaboration
  -}

  elab-cbv : Elab (Lam ∔ Lift State ∔ Lift Nil) (State ⊕ Nil)
  elab-cbv = auto-elab

  {-
  The program evaluates using a call-by-value interpretation
  -}
  test-ex-cbv : un ((given hSt handle (elab elab-cbv ex)) 0) ≡ 4
  test-ex-cbv = refl


{-
A call-by-name interpretation of the universe of types
-}

module CBNInterpretation where

  {-
  A universe of types with functions, numbers, and thunks (suspended computations)
  -}

  data Type : Set where
    _⟶_ : (t₁ t₂ : Type)   → Type
    num  :                     Type
    susp : Type              → Type

  private instance
    CBNUniverse : Universe
    Ty ⦃ CBNUniverse ⦄ = Type
    ⟦_⟧ ⦃ CBNUniverse ⦄ (t ⟶ t₁)  = ⟦ t ⟧ → Free (State ⊕ Nil) ⟦ t₁ ⟧
    ⟦_⟧ ⦃ CBNUniverse ⦄ num        = ℕ
    ⟦_⟧ ⦃ CBNUniverse ⦄ (susp t)   = Free (State ⊕ Nil) ⟦ t ⟧


    {-
    The call-by-name interpretation adheres to the LamUniverse interface from
    `Hefty.Lambda`
    -}

    iso-num : ℕ ↔ ⟦ num ⟧
    iso-num = ↔-id _

    iso-fun : {t₁ t₂ : Type}
            → (⟦ t₁ ⟧ → Free (State ⊕ Nil) ⟦ t₂ ⟧) ↔ ⟦ t₁ ⟶ t₂ ⟧
    iso-fun = ↔-id _

    iso-susp : {t : Ty}
             → Free (State ⊕ Nil) ⟦ t ⟧ ↔ ⟦ susp t ⟧
    iso-susp = ↔-id _

    LamCBNUniverse : LamUniverse
    u ⦃ LamCBNUniverse ⦄ = CBNUniverse
    _↣_ ⦃ LamCBNUniverse ⦄ = _⟶_
    c ⦃ LamCBNUniverse ⦄ = susp


  {-
  Automatic elaboration
  -}

  elab-cbn : Elab (Lam ∔ Lift State ∔ Lift Nil) (State ⊕ Nil)
  elab-cbn = auto-elab


  {-
  The program evaluates using a call-by-value interpretation
  -}
  test-ex-cbv : un ((given hSt handle (elab elab-cbn ex)) 0) ≡ 5
  test-ex-cbv = refl

