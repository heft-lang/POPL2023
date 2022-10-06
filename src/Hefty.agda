module Hefty where

open import Function
open import Level using (Level; zero; _⊔_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ zero zero
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)

open import Free hiding (_>>=_; _>>_)
open import Free.Nil


---------------------
--- PRELIMINARIES ---
---------------------

variable
  m n : Level
  F F₀ F₁ F₂ F₃ : Set n → Set (n ⊔ m)


----------------------------
--- HIGHER-ORDER EFFECTS ---
----------------------------

{-
A higher-order effect signature (`Effectᴴ`) is a dependent tuple of a type of
operations (`Op`), a function (`Fork`) that associates an effect signature
describing the shape of sub-computations with each operation, and a function
(`Ret`) that associates a return type with each operation.
-}

record Effectᴴ : Set₁ where
  field  Op     : Set
         Fork   : Op → Effect
         Ret    : Op → Set

open Effectᴴ public

variable H H′ H″ H‴ H₀ H₁ H₂ H₃ H₄ : Effectᴴ


{-
Higher-order effects can be summed by taking their (disjoint) union.
-}

infixr 12 _∔_

_∔_ : Effectᴴ → Effectᴴ → Effectᴴ
Op     (H₁ ∔ H₂)                = Op H₁ ⊎ Op H₂
Fork   (H₁ ∔ H₂)                = [ Fork H₁  , Fork H₂  ]
Ret    (H₁ ∔ H₂)                = [ Ret H₁   , Ret H₂   ]


-------------------
--- HEFTY TREES ---
-------------------

{-
A hefty tree over a higher-order effect signature is either a `pure` computation
which simply yields a value of the expected type, or an `impure` computation
comprising an `op`eration of the effect signature, a fork (`ψ`) containing the
computational arguments of the operation, and a `k`ontinuation which expects a
value of the return type of the `op`eration.
-}

data Hefty (H : Effectᴴ) (A : Set) : Set where
  pure    :  A → Hefty H A
  impure  :  (op  : Op H)
             (ψ   : (s : Op (Fork H op)) → Hefty H (Ret (Fork H op) s))
             (k   : Ret H op → Hefty H A)
          →  Hefty H A


{-

A hefty algebra (`Alg`)

-}

record Alg (H : Effectᴴ) (G : Set → Set) : Set₁ where
  constructor mkAlg
  field alg  :  (op  : Op H)
                (ψ   : (s : Op (Fork H op)) → G (Ret (Fork H op) s))
                (k   : Ret H op → G A)
             →  G A

open Alg public


{-
The free monad can be folded using the following recursion scheme
(catamorphism):
-}

cataᴴ : (∀ {A} → A → F A) → Alg H F → Hefty H A → F A
cataᴴ g a (pure x)         = g x
cataᴴ g a (impure op ψ k)  = alg a op (cataᴴ g a ∘ ψ) (cataᴴ g a ∘ k)

{-
We cannot define bind using cataᴴ directly since cataᴴ folds over sub-trees.
Bind should _not_ be distributed over sub-trees (`ψ`); _only_ over continuations
(`k`).  We define bind directly:
-}

_>>=_ : Hefty H A → (A → Hefty H B) → Hefty H B
pure x         >>= g = g x
impure op ψ k  >>= g = impure op ψ (λ x → k x >>= g)

_>>_ : Hefty H A → Hefty H B → Hefty H B
m₁ >> m₂ = m₁ >>= λ _ → m₂


{-
We define fmap similarly.
-}

fmapᴴ : (A → B) → Hefty H A → Hefty H B
fmapᴴ f (pure x) = pure (f x)
fmapᴴ f (impure op ψ k) = impure op ψ (fmapᴴ f ∘ k)


{-
Note: Higher-order signatures are a container-ized encoding of a _higher-order
functor_; that is, it is encoding objects of type `H : (Set → Set) → (Set →
Set)` which have both the usual functorial `map : (X → Y) → H F X → H F Y` for
any functor `F` but also `hmap : Nat(F, G) → Nat(H F, H G)` which lifts natural
transformations to H objects for any functors `F` and `G`.

We leave it as an exercise for the interested reader to define the hmap for the
container encoding.  The Haskell encoding in the `haskell` sub-folder at the
top-level of this repository contains an encoding of this function.  (That
encoding cannot be used directly in Agda because of strict positivity issues.)
-}


----------------------
--- ROW INSERTIONS ---
----------------------

{-
The row insertion witnesses we defined in `Free.agda` is straightforwardly
ported to the higher-order effect setting.
-}

data _∼_▹_ : Effectᴴ → Effectᴴ → Effectᴴ → Set₁ where
  insert  :                 (H₀ ∔ H′)  ∼ H₀ ▹ H′
  sift    : H ∼ H₀ ▹ H′  →  (H₁ ∔ H)   ∼ H₀ ▹ (H₁ ∔ H′)


{-
We add the row insertion witness constructors as instance arguments to aid
automation.
-}

instance
  insert▹ : (H₀ ∔ H′) ∼ H₀ ▹ H′
  insert▹ = insert

  sift▹ : ⦃ H ∼ H₀ ▹ H′ ⦄  →  (H₁ ∔ H)   ∼ H₀ ▹ (H₁ ∔ H′)
  sift▹ ⦃ w ⦄ = sift w


{-
Some helper functions and lemmas using row insertion witnesses.

(Only a subset of these are actually used in this artifact.)
-}

inj▹ₗ : ⦃ H ∼ H₀ ▹ H′ ⦄ → Op H₀  → Op H
inj▹ₗ ⦃ insert ⦄  = inj₁
inj▹ₗ ⦃ sift p ⦄  = inj₂ ∘ inj▹ₗ ⦃ p ⦄

inj▹ᵣ : ⦃ H ∼ H₀ ▹ H′ ⦄ → Op H′  → Op H
inj▹ᵣ ⦃ insert ⦄  = inj₂
inj▹ᵣ ⦃ sift p ⦄  = [ inj₁ , inj₂ ∘ inj▹ᵣ ⦃ p ⦄ ]



inj▹ₗ-ret≡ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ (op : Op H₀)
           → Ret H (inj▹ₗ op) ≡ Ret H₀ op
inj▹ₗ-ret≡ ⦃ insert ⦄ _  = refl
inj▹ₗ-ret≡ ⦃ sift p ⦄    = inj▹ₗ-ret≡ ⦃ p ⦄

inj▹ᵣ-ret≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ (op : Op H′)
          → Ret H (inj▹ᵣ op) ≡ Ret H′ op
inj▹ᵣ-ret≡ ⦃ insert ⦄ op  = refl
inj▹ᵣ-ret≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▹ᵣ-ret≡ ⦃ p ⦄ ]

inj▹ₗ-fork≡ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ (op : Op H₀)
              → Fork H (inj▹ₗ op) ≡ Fork H₀ op
inj▹ₗ-fork≡ ⦃ insert ⦄ _  = refl
inj▹ₗ-fork≡ ⦃ sift p ⦄    = inj▹ₗ-fork≡ ⦃ p ⦄

inj▹ᵣ-fork≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ (op : Op H′)
              → Fork H (inj▹ᵣ op) ≡ Fork H′ op
inj▹ᵣ-fork≡ ⦃ insert ⦄ op  = refl
inj▹ᵣ-fork≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▹ᵣ-fork≡ ⦃ p ⦄ ]

inj▹ₗ-prong≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} (b : Op (Fork H (inj▹ₗ op)))
              → Ret (Fork H (inj▹ₗ op)) b ≡ Ret (Fork H₀ op) (subst Op (inj▹ₗ-fork≡ ⦃ p ⦄ op) b)
inj▹ₗ-prong≡ ⦃ insert ⦄ op  = refl
inj▹ₗ-prong≡ ⦃ p = sift p ⦄ {op} b = inj▹ₗ-prong≡ ⦃ p ⦄ b

inj▹ₗ-prong2≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} (b : Op (Fork H₀ op))
              → Ret (Fork H₀ op) b ≡ Ret (Fork H (inj▹ₗ op)) (subst Op (sym $ inj▹ₗ-fork≡ ⦃ p ⦄ op) b)
inj▹ₗ-prong2≡ ⦃ insert ⦄ op  = refl
inj▹ₗ-prong2≡ ⦃ p = sift p ⦄ {op} b = inj▹ₗ-prong2≡ ⦃ p ⦄ b

inj▹ᵣ-prong2≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} (b : Op (Fork H′ op))
              → Ret (Fork H′ op) b ≡ Ret (Fork H (inj▹ᵣ op)) (subst Op (sym $ inj▹ᵣ-fork≡ ⦃ p ⦄ op) b)
inj▹ᵣ-prong2≡ ⦃ insert ⦄ op  = refl
inj▹ᵣ-prong2≡ ⦃ p = sift p ⦄ {inj₁ x} b = refl
inj▹ᵣ-prong2≡ ⦃ p = sift p ⦄ {inj₂ x} b = inj▹ᵣ-prong2≡ ⦃ p ⦄ b

inj▹ᵣ-prong≡ : ⦃ p : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} (b : Op (Fork H (inj▹ᵣ op)))
             → Ret (Fork H (inj▹ᵣ op)) b ≡ Ret (Fork H′ op) (subst Op (inj▹ᵣ-fork≡ ⦃ p ⦄ op) b)
inj▹ᵣ-prong≡ ⦃ insert ⦄ op  = refl
inj▹ᵣ-prong≡ ⦃ p = sift p ⦄ {inj₁ x} b = refl
inj▹ᵣ-prong≡ ⦃ p = sift p ⦄ {inj₂ y} b = inj▹ᵣ-prong≡ ⦃ p ⦄ b

proj-ret▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} → Ret H (inj▹ₗ op) → Ret H₀ op
proj-ret▹ₗ ⦃ w = insert ⦄ = id
proj-ret▹ₗ ⦃ w = sift w ⦄ = proj-ret▹ₗ ⦃ w ⦄

proj-ret2▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀} → Ret H₀ op → Ret H (inj▹ₗ op)
proj-ret2▹ₗ ⦃ w = insert ⦄ = id
proj-ret2▹ₗ ⦃ w = sift w ⦄ = proj-ret2▹ₗ ⦃ w ⦄

proj-ret▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} → Ret H (inj▹ᵣ op) → Ret H′ op
proj-ret▹ᵣ ⦃ w = insert ⦄ = id
proj-ret▹ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
proj-ret▹ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret▹ᵣ ⦃ w ⦄

proj-ret2▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′} → Ret H′ op → Ret H (inj▹ᵣ op)
proj-ret2▹ᵣ ⦃ w = insert ⦄ = id
proj-ret2▹ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
proj-ret2▹ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret2▹ᵣ ⦃ w ⦄

proj-fork▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀}
              → ((b : Op (Fork H₀ op)) → Hefty H (Ret (Fork H₀ op) b))
              → ((b : Op (Fork H (inj▹ₗ op))) → Hefty H (Ret (Fork H (inj▹ₗ op)) b))
proj-fork▹ₗ ⦃ w ⦄ {op} f b  =
  let x = f (subst Op (inj▹ₗ-fork≡ ⦃ w ⦄ op) b) in
  subst (Hefty _) (sym $ inj▹ₗ-prong≡ ⦃ w ⦄ b) x

proj-fork2▹ₗ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H₀}
              → ((b : Op (Fork H (inj▹ₗ op))) → Hefty H″ (Ret (Fork H (inj▹ₗ op)) b))
              → ((b : Op (Fork H₀ op)) → Hefty H″ (Ret (Fork H₀ op) b))
proj-fork2▹ₗ ⦃ w ⦄ {op} f b  =
  let x = f (subst Op (sym $ inj▹ₗ-fork≡ ⦃ w ⦄ op) b) in
  subst (Hefty _) (sym $ inj▹ₗ-prong2≡ ⦃ w ⦄ b) x

proj-fork▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′}
              → ((b : Op (Fork H′ op)) → Hefty H″ (Ret (Fork H′ op) b))
              → ((b : Op (Fork H (inj▹ᵣ op))) → Hefty H″ (Ret (Fork H (inj▹ᵣ op)) b))
proj-fork▹ᵣ ⦃ w ⦄ {op} f b  =
  let x = f (subst Op (inj▹ᵣ-fork≡ ⦃ w ⦄ op) b) in
  subst (Hefty _) (sym $ inj▹ᵣ-prong≡ ⦃ w ⦄ b) x

proj-fork2▹ᵣ : ⦃ w : H ∼ H₀ ▹ H′ ⦄ {op : Op H′}
              → ((b : Op (Fork H (inj▹ᵣ op))) → Hefty H″ (Ret (Fork H (inj▹ᵣ op)) b))
              → ((b : Op (Fork H′ op)) → Hefty H″ (Ret (Fork H′ op) b))
proj-fork2▹ᵣ ⦃ w ⦄ {op} f b  =
  let x = f (subst Op (sym $ inj▹ᵣ-fork≡ ⦃ w ⦄ op) b) in
  subst (Hefty _) (sym $ inj▹ᵣ-prong2≡ ⦃ w ⦄ b) x


case▹  :  ⦃ H ∼ H₀ ▹ H′ ⦄
       →  Op H
       →  (Op H₀ → B)
       →  (Op H′ → B)
       →  B
case▹ ⦃ insert ⦄ x f g = [ f , g ] x
case▹ ⦃ sift p ⦄ x f g = [ g ∘ inj₁ , (λ y → case▹ ⦃ p ⦄ y f (g ∘ inj₂ )) ] x

case▹≡  :  ⦃ w : H ∼ H₀ ▹ H′ ⦄
       →  (op : Op H)
       →  ((op′ : Op H₀) → op ≡ inj▹ₗ op′ → B)
       →  ((op′ : Op H′) → op ≡ inj▹ᵣ op′ → B)
       →  B
case▹≡ ⦃ w = insert ⦄ (inj₁ x) f g = f x refl
case▹≡ ⦃ w = insert ⦄ (inj₂ y) f g = g y refl
case▹≡ ⦃ w = sift p ⦄ (inj₁ x) f g = g (inj₁ x) refl
case▹≡ ⦃ w = sift p ⦄ (inj₂ y) f g = case▹≡ ⦃ p ⦄ y (λ op′ → f op′ ∘ cong inj₂) (λ op′ → g (inj₂ op′) ∘ cong inj₂)


-------------------
--- ELABORATION ---
-------------------

{-
An elaboration `Elab H ε` is an algebra over H that elaborates into an algebraic
effect tree (`Free`) with effects ε.
-}

Elaboration : Effectᴴ → Effect → Set₁
Elaboration H ε = Alg H (Free ε)


{-
Algebras are closed under higher order effect signature sum.
-}

infixr 12 _⋎_
_⋎_ : Alg H₁ F → Alg H₂ F → Alg (H₁ ∔ H₂) F
alg (A₁ ⋎ A₂) (inj₁ op) = alg A₁ op
alg (A₁ ⋎ A₂) (inj₂ op) = alg A₂ op

{-
Elaborations elaborate higher-order effect trees into algebraic effect trees.
-}

elaborate : Elaboration H ε → Hefty H A → Free ε A
elaborate = cataᴴ pure


{-
Elaborations can be automated
-}

record Elab (H : Effectᴴ) (ε : Effect) : Set₁ where
  field orate : Alg H (Free ε)

open Elab public

elab  : Elab H ε → Hefty H A → Free ε A
elab = elaborate ∘ orate

instance
  auto-elab : ⦃ E₁ : Elab H₁ ε ⦄ ⦃ E₂ : Elab H₂ ε ⦄ → Elab (H₁ ∔ H₂) ε
  orate (auto-elab ⦃ E₁ ⦄ ⦃ E₂ ⦄) = (orate E₁) ⋎ (orate E₂)
