{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Hefty.Catch+Throw+State where

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

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Lift
open import Hefty.Catch
open import Hefty.Nil

open import Free hiding (_>>=_; _>>_)
open import Free.Throw
open import Free.State ℕ
open import Free.Nil


{-
A universe of types
-}

data Type : Set where
  unit  : Type
  num   : Type

instance
  TypeUniverse : Universe
  T  ⦃ TypeUniverse ⦄ = Type
  ⟦_⟧ ⦃ TypeUniverse ⦄ unit = ⊤
  ⟦_⟧ ⦃ TypeUniverse ⦄ num  = ℕ


{-
A smarter constructor for ↑ throw
-}

‵throwᴴ : ⦃ w : H  ∼  Lift Throw  ▹ H″ ⦄
         → Hefty H A
‵throwᴴ ⦃ w ⦄ = (↑ throw) >>= ⊥-elim
  where open import Hefty using (_>>=_)


{-
An example
-}

transact  :  ⦃ wₛ  : H  ∼  Lift State  ▹ H′ ⦄ ⦃ wₜ  : H  ∼  Lift Throw  ▹ H″ ⦄ ⦃ w   : H  ∼  Catch       ▹ H‴ ⦄
          →  Hefty H ℕ
transact = do
  ↑ (put 1)
  ‵catch (do ↑ (put 2); (↑ throw) >>= ⊥-elim) (pure tt)
  ↑ get
  where open import Hefty using (_>>=_; _>>_)


{-
Building elaboration from component parts
-}

transact-elab : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
transact-elab = eLift ⋎ eLift ⋎ eCatch ⋎ eNil

transact-elab′ : Elaboration (Lift State ∔ Lift Throw ∔ Catch ∔ Lift Nil) (State ⊕ Throw ⊕ Nil)
transact-elab′ = orate auto-elab -- same as above, but automated


{-
A test
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
An alternative interpretation of the original program.

In other words, Catch is an interface whose operational implementation we can
change, modularly.
-}

test-transact₁ : end (handle₀ hThrow (handle hSt (elaborate transact-elab₁ transact) 0))
                 ≡ nothing
test-transact₁ = refl


