{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Example.Hefty.Censor+Output where

open import Level renaming (zero to ℓ0) using ()
open import Function
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Product
open import Data.Nat hiding (_≟_)
open import Data.String
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to Ty; El to ⟦_⟧)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Free  hiding (_>>=_; _>>_)
open import Free.Output
open import Free.Nil

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Lift
open import Hefty.Censor
open import Hefty.Nil

{-
A simple universe of types
-}

data Type : Set where
  unit : Type
  num : Type

instance
  SimpleUniverse : Universe
  Ty ⦃ SimpleUniverse ⦄ = Type
  ⟦_⟧ ⦃ SimpleUniverse ⦄ unit = ⊤
  ⟦_⟧ ⦃ SimpleUniverse ⦄ num = ℕ


{-
Elaborations
-}

censor-elab : Elaboration (Censor ∔ Lift Output ∔ Lift Nil) (Output ⊕ Nil)
censor-elab = eCensor ⋎ eLift ⋎ eNil

censor′-elab : Elaboration (Censor ∔ Lift Output ∔ Lift Nil) (Output ⊕ Nil)
censor′-elab = eCensor′ ⋎ eLift ⋎ eNil


{-
Example programs
-}

hello : ⦃ w : H ∼ Lift Output ▹ H″ ⦄
      → Hefty H ⊤
hello = do ↑ out "Hello"; ↑ out " world!"
  where open import Hefty using (_>>_)

censorHello : ⦃ w₁ : H ∼ Censor ▹ H′ ⦄ ⦃ w₂ : H ∼ Lift Output ▹ H″ ⦄
            → Hefty H ⊤
censorHello = ‵censor
  (λ s → case (s ≟ "Hello") of λ where
           (yes _) → "Goodbye"
           (no  _) → s)
  hello


test-censor : un ( ( given hOut
                     handle (elaborate censor-elab censorHello) ) tt )
                ≡ (tt , "Hello world!")
test-censor = refl


test-censor′ : un ( ( given hOut
                     handle (elaborate censor′-elab censorHello) ) tt )
                ≡ (tt , "Goodbye world!")
test-censor′ = refl
