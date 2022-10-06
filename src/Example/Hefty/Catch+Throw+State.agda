{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Hefty.Catch+Throw+State where

open import Function
open import Level renaming (zero to ℓ0) using ()
open import Data.Empty
open import Data.Unit
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing)
open import Data.Nat
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)
open import Relation.Binary.PropositionalEquality
open import Function.Construct.Identity using (↔-id)

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Lift
open import Hefty.Catch
open import Hefty.Nil

open import Free hiding (_>>=_; _>>_)
open import Free.Throw
open import Free.State ℕ
open import Free.SubJump
open import Free.Nil


{-
A universe of types polymorphic program with state and exceptions.  Under a
"global state" semantics of exception handling, the program returns 2.  Under a
"transactional state" semantics of exception handling, the program returns 1.
-}

module _ ⦃ u : Universe ⦄ {unit : T} ⦃ iso : ⟦ unit ⟧ ↔ ⊤ ⦄ where

  open import Hefty using (_>>=_; _>>_)
  open Inverse ⦃ ... ⦄

  transact : ⦃ wₛ : H ∼ Lift State ▹ H′ ⦄ ⦃ wₜ : H ∼  Lift Throw ▹ H″ ⦄ ⦃ w  : H ∼ Catch ▹ H‴ ⦄
           → Hefty H ℕ
  transact = do
    ↑ put 1
    ‵catch (do ↑ put 2; ‵throwᴴ) (pure (from tt))
    ↑ get



{-
A simple universe of types
-}

data Type : Set where
  unit  : Type
  num   : Type

instance
  TypeUniverse : Universe
  T  ⦃ TypeUniverse ⦄ = Type
  ⟦_⟧ ⦃ TypeUniverse ⦄ unit = ⊤
  ⟦_⟧ ⦃ TypeUniverse ⦄ num  = ℕ

  iso-unit : ⟦ unit ⟧ ↔ ⊤
  iso-unit = ↔-id _



{-
A global state interpretation of the program
-}

module GlobalStateInterpretation where

  {-
  Building elaboration from component parts
  -}

  transact-elab : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
  transact-elab = eLift ⋎ eLift ⋎ eCatch ⋎ eNil

  transact-elab′ : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
  transact-elab′ = orate auto-elab -- same as above, but automated
    where instance
      eCatch′ : Elab Catch (State ⊕ Throw ⊕ Nil)
      orate eCatch′ = eCatch


  {-
  Test showing that the program has a global state semantics
  -}

  test-transact : end (handle₀ hThrow (handle hSt (elaborate transact-elab′ transact) 0))
                  ≡ just 2
  test-transact = refl


  {-
  An alternative elaboration for catch
  -}

  eCatch₁ : ⦃ u : Universe ⦄ ⦃ w : ε ∼ Throw ▸ ε′ ⦄ →  Elaboration (Catch ⦃ TypeUniverse ⦄) ε
  alg eCatch₁ (catch t) ψ k = (ψ true) >>= k
    where open import Free using (_>>=_)

  transact-elab₁ : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
  transact-elab₁ = eLift ⋎ eLift ⋎ eCatch₁ ⋎ eNil


  {-
  An alternative interpretation of the original program, showing that Catch is
  an interface whose operational implementation we can change, modularly.
  -}

  test-transact₁ : end (handle₀ hThrow (handle hSt (elaborate transact-elab₁ transact) 0))
                   ≡ nothing
  test-transact₁ = refl


{-
An optionally-transactional state interpretation of the program
-}

module TransactionalStateInterpretation where

  open Inverse ⦃ ... ⦄

  transact-elab₂ : Elab  (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil)
                         (CC (λ t → ⟦ t ⟧ → Free Nil A) ⊕ State ⊕ Throw ⊕ Nil)
  transact-elab₂ = auto-elab
    where instance
      eCatchCC′ : Elab Catch _
      orate eCatchCC′ = eCatchCC

  transact-elab₃ : Elab (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil)
                        (CC (λ t → ⟦ t ⟧ → Free (State ⊕ Nil) A) ⊕ State ⊕ Throw ⊕ Nil)
  transact-elab₃ = auto-elab
    where instance
      eCatchCC′ : Elab Catch _
      orate eCatchCC′ = eCatchCC


  {-
  Running the state handler before throw gives a transactional state interpretation
  -}

  test-transact₂ :  end (handle₀! hCC (handle₀ hThrow (handle hSt (elab transact-elab₂ transact) 0)))
                      ≡ just 1
  test-transact₂ = refl

  {-
  Running the throw handler before the state handler gives a global state interpretation
  -}

  test-transact₃ : end (handle hSt (handle₀! hCC (handle₀ hThrow (elab transact-elab₃ transact))) 0) ≡ just 2
  test-transact₃ = refl


  {-
  More tests
  -}

  transact′ : ⦃ wₛ : H ∼ Lift State ▹ H′ ⦄ ⦃ wₜ : H ∼  Lift Throw ▹ H″ ⦄ ⦃ w  : H ∼ Catch ▹ H‴ ⦄
            → Hefty H ℕ
  transact′ = do
    ↑ put 1
    ‵catch (do ↑ put 2) (pure (from tt))
    ↑ get
    where open import Hefty using (_>>_)

  test-transact₂′ : end (handle₀! hCC (handle₀ hThrow (handle hSt (elab transact-elab₂ transact′) 0))) ≡ just 2
  test-transact₂′ = refl

  test-transact₃′ : end (handle hSt (handle₀! hCC (handle₀ hThrow (elab transact-elab₃ transact′))) 0) ≡ just 2
  test-transact₃′ = refl


  transact″ : ⦃ wₛ : H ∼ Lift State ▹ H′ ⦄ ⦃ wₜ : H ∼  Lift Throw ▹ H″ ⦄ ⦃ w  : H ∼ Catch ▹ H‴ ⦄
            → Hefty H ℕ
  transact″ = do
    ↑ put 1
    ‵catch (do ↑ put 2; ‵throwᴴ) (↑ get)
    where open import Hefty using (_>>_)

  test-transact₂″ : end (handle₀! hCC (handle₀ hThrow (handle hSt (elab transact-elab₂ transact″) 0))) ≡ just 1
  test-transact₂″ = refl

  test-transact₃″ : end (handle hSt (handle₀! hCC (handle₀ hThrow (elab transact-elab₃ transact″))) 0) ≡ just 2
  test-transact₃″ = refl
