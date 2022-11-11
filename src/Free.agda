module Free where

open import Level using (Level)
open import Function
open import Data.Unit
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Postulate.Extensionality


---------------------
--- PRELIMINARIES ---
---------------------

{-
The `variable` keyword tells Agda to implicitly add quantifiers over the
following names when they occur free in type signatures:
-}

variable a b : Level
         A B C D X Y Z P : Set a
         G : Set → Set


---------------
--- EFFECTS ---
---------------

{-
An effect signature (`Effect`) is a dependent pair of a type of operations
(`Op`), and a function (`Ret`) that associates a return type with each
operation.

(This encoding is also known as a "container".)
-}

record Effect : Set₁ where
  field  Op   : Set
         Ret  : Op → Set

open Effect public

variable Δ Δ′ Δ″ Δ‴ Δ₀ Δ₁ Δ₂ Δ₃ : Effect


{-
Effects can be summed by taking their (disjoint) union.
-}

infixr 12 _⊕_
_⊕_ : Effect → Effect → Effect
Op (Δ₁ ⊕ Δ₂) = Op Δ₁ ⊎ Op Δ₂
Ret (Δ₁ ⊕ Δ₂) = [ Ret Δ₁ , Ret Δ₂ ]


------------------
--- FREE MONAD ---
------------------


{-
The free monad over an effect signature is either a `pure` computation which
simply yields a value of the expected type, or an `impure` computation
comprising an `op`eration of the effect signature, and a `k`ontinuation which
expects a value of the return type of the `op`eration.

(This encoding of the free monad is due to Hancock and Setzer.)
-}

data Free (Δ : Effect) (A : Set) : Set where
  pure    : A                                      → Free Δ A
  impure  : (op : Op Δ) (k : Ret Δ op → Free Δ A)  → Free Δ A


{-
The free monad can be folded using the following recursion scheme:
-}

fold : (A → B) → ((op : Op Δ) (k : Ret Δ op → B) → B) → Free Δ A → B
fold gen alg (pure x)       = gen x
fold gen alg (impure op k)  = alg op (fold gen alg ∘ k)


{-
Using `fold`, we can map and bind free monadic computations:
-}
fmap : (A → B) → Free Δ A → Free Δ B
fmap f = fold (pure ∘ f) impure

_>>=_ : Free Δ A → (A → Free Δ B) → Free Δ B
m >>= g = fold g impure m

_>>_ : Free Δ A → Free Δ B → Free Δ B
m₁ >> m₂ = m₁ >>= λ _ → m₂


{-
Some lemmas about fold and bind:
-}

fold≡ : (m : Free Δ A) → fold pure impure m ≡ m
fold≡ (pure x) = refl
fold≡ (impure op k) = cong (impure op) (extensionality (λ x → fold≡ (k x)))

Free-unitₗ-≡ : {x : A} (k : A → Free Δ B)
             → pure x >>= k ≡ k x
Free-unitₗ-≡ _ = refl

Free-unitᵣ-≡ : (m : Free Δ A)
             → m >>= pure ≡ m
Free-unitᵣ-≡ (pure x) = refl
Free-unitᵣ-≡ (impure op k) = cong (λ x → impure op x) (extensionality $ λ y → Free-unitᵣ-≡ $ k y) 

Free-assoc-≡ : (m : Free Δ A) (k₁ : A → Free Δ B) (k₂ : B → Free Δ C)
             → (m >>= k₁) >>= k₂ ≡ m >>= (λ x → (k₁ x) >>= k₂)
Free-assoc-≡ (pure x) k₁ k₂ = refl
Free-assoc-≡ (impure op k) k₁ k₂ = cong (λ x → impure op x) (extensionality $ λ x → Free-assoc-≡ (k x) k₁ k₂)

Free-cong₂ : (m : Free Δ A) (k k' : A → Free Δ B)
           → (∀ x → k x ≡ k' x)
           → (m >>= k) ≡ (m >>= k')
Free-cong₂ (pure x) k k' eq = eq _
Free-cong₂ (impure op k₁) k k' eq = cong (λ x → impure op x) $ extensionality $ λ x →
  cong (λ y → (k₁ x) >>= y) $ extensionality eq


----------------------
--- ROW INSERTIONS ---
----------------------

{-
A row insertion witness Δ ∼ Δ₀ ▸ Δ′ is a proof relevant witness that (1) Δ is
given by a "row" of summed effects, and (2) Δ can be obtained by inserting Δ₀
into the row Δ′.
-}

data _∼_▸_ : Effect → Effect → Effect → Set₁ where
  insert :                 (Δ₀ ⊕ Δ′) ∼ Δ₀ ▸ Δ′
  sift   : (Δ ∼ Δ₀ ▸ Δ′) → ((Δ₁ ⊕ Δ) ∼ Δ₀ ▸ (Δ₁ ⊕ Δ′))


{-
We add the row insertion witness constructors as instances to allow Agda to
infer row instance witnesses for us.

The two constructors overlap, so proof search using these witnesses is only
useful if we use the Agda flag `--overlapping-instances`.
-}

instance
  insert▸ : (Δ₀ ⊕ Δ′) ∼ Δ₀ ▸ Δ′
  insert▸ = insert

  sift▸ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → ((Δ₁ ⊕ Δ) ∼ Δ₀ ▸ (Δ₁ ⊕ Δ′))
  sift▸ ⦃ w ⦄ = sift w


{-
Some helper functions and lemmas using row insertion witnesses.
-}

inj▸ₗ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → Op Δ₀  → Op Δ
inj▸ᵣ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → Op Δ′  → Op Δ

inj▸ₗ ⦃ insert ⦄  = inj₁
inj▸ₗ ⦃ sift p ⦄  = inj₂ ∘ inj▸ₗ ⦃ p ⦄

inj▸ᵣ ⦃ insert ⦄  = inj₂
inj▸ᵣ ⦃ sift p ⦄  = [ inj₁ , inj₂ ∘ inj▸ᵣ ⦃ p ⦄ ]

proj-ret▸ₗ : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ {op : Op Δ₀} → Ret Δ (inj▸ₗ op) → Ret Δ₀ op
proj-ret▸ₗ ⦃ w = insert ⦄ = id
proj-ret▸ₗ ⦃ w = sift w ⦄ = proj-ret▸ₗ ⦃ w ⦄

proj-ret▸ᵣ : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ {op : Op Δ′} → Ret Δ (inj▸ᵣ op) → Ret Δ′ op
proj-ret▸ᵣ ⦃ w = insert ⦄ = id
proj-ret▸ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
proj-ret▸ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret▸ᵣ ⦃ w ⦄

inj▸ₗ-ret≡ : ⦃ p : Δ ∼ Δ₀ ▸ Δ′ ⦄ (op : Op Δ₀)
           → Ret Δ (inj▸ₗ op) ≡ Ret Δ₀ op
inj▸ₗ-ret≡ ⦃ insert ⦄ _  = refl
inj▸ₗ-ret≡ ⦃ sift p ⦄    = inj▸ₗ-ret≡ ⦃ p ⦄

inj▸ᵣ-ret≡ : ⦃ p : Δ ∼ Δ₀ ▸ Δ′ ⦄ (op : Op Δ′)
           → Ret Δ (inj▸ᵣ op) ≡ Ret Δ′ op
inj▸ᵣ-ret≡ ⦃ insert ⦄ op  = refl
inj▸ᵣ-ret≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▸ᵣ-ret≡ ⦃ p ⦄ ]

case▸ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄
      → Op Δ
      → (Op Δ₀  → B)
      → (Op Δ′  → B)
      → B
case▸ ⦃ insert ⦄ x f g = [ f , g ] x
case▸ ⦃ sift p ⦄ x f g = [ g ∘ inj₁ , (λ y → case▸ ⦃ p ⦄ y f (g ∘ inj₂)) ] x

case▸≡ : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄
       → (op : Op Δ)
       → ((op′ : Op Δ₀) → op ≡ inj▸ₗ op′ → B)
       → ((op′ : Op Δ′) → op ≡ inj▸ᵣ op′ → B)
       → B
case▸≡ ⦃ w = insert ⦄ (inj₁ x) f g = f x refl
case▸≡ ⦃ w = insert ⦄ (inj₂ y) f g = g y refl
case▸≡ ⦃ w = sift p ⦄ (inj₁ x) f g = g (inj₁ x) refl
case▸≡ ⦃ w = sift p ⦄ (inj₂ y) f g = case▸≡ ⦃ p ⦄ y (λ op′ → f op′ ∘ cong inj₂) (λ op′ → g (inj₂ op′) ∘ cong inj₂)

to-front : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ → Free Δ A → Free (Δ₀ ⊕ Δ′) A
to-front {Δ₀ = Δ₀} ⦃ w ⦄ (pure x) = pure x
to-front {Δ₀ = Δ₀} ⦃ insert ⦄ (impure op k) = impure op (to-front ⦃ insert ⦄ ∘ k)
to-front {Δ₀ = Δ₀} ⦃ sift w ⦄ (impure (inj₁ op) k) = impure (inj₂ (inj₁ op)) (to-front ⦃ sift w ⦄ ∘ k)
to-front {Δ₀ = Δ₀} ⦃ sift {Δ = Δ} {Δ′ = Δ′} w ⦄ t@(impure (inj₂ op) k) = case▸≡ ⦃ w ⦄ op
  (λ op′ eq →
    impure
      (inj₁ op′)
      ( to-front ⦃ sift w ⦄
      ∘ k
      ∘ subst id (begin
          Ret Δ₀ op′
        ≡⟨ sym (inj▸ₗ-ret≡ ⦃ w ⦄ op′) ⟩
          Ret Δ (inj▸ₗ ⦃ w ⦄ op′)
        ≡⟨ sym $ cong (Ret Δ) eq ⟩
          Ret Δ op
        ∎)))
  (λ op′ eq →
    impure (inj₂ (inj₂ op′))
      ( to-front ⦃ sift w ⦄
      ∘ k
      ∘ subst id (begin
          Ret Δ′ op′
        ≡⟨ sym (inj▸ᵣ-ret≡ ⦃ w ⦄ op′) ⟩
          Ret Δ (inj▸ᵣ ⦃ w ⦄ op′)
        ≡⟨ (sym $ cong (Ret Δ) eq) ⟩
          Ret Δ op
        ∎)))

from-front : ⦃ w : Δ ∼ Δ₀ ▸ Δ′ ⦄ → Free (Δ₀ ⊕ Δ′) A → Free Δ A
from-front ⦃ w = w ⦄ (pure x) = pure x
from-front ⦃ w = w ⦄ (impure (inj₁ op) k) = impure (inj▸ₗ op) (from-front ∘ k ∘ proj-ret▸ₗ ⦃ w ⦄)
from-front ⦃ w = w ⦄ (impure (inj₂ op) k) = impure (inj▸ᵣ op) (from-front ∘ k ∘ proj-ret▸ᵣ ⦃ w ⦄)


----------------
--- HANDLERS ---
----------------

Alg : (Δ : Effect) (A : Set) → Set
Alg Δ A = (op : Op Δ) (k : Ret Δ op → A) → A

record ⟨_!_⇒_⇒_!_⟩ (A : Set) (Δ : Effect) (P : Set) (B : Set) (Δ′ : Effect) : Set₁ where
  field  ret  : A → P → Free Δ′ B
         hdl  : Alg Δ (P → Free Δ′ B)

open ⟨_!_⇒_⇒_!_⟩ public

given_handle_ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → ⟨ A ! Δ₀ ⇒ P ⇒ B ! Δ′ ⟩ → Free Δ A → (P → Free Δ′ B)
given h handle m = fold
  (ret h)
  [ hdl h , (λ op k p → impure op (λ x → k x p)) ]
  (to-front m)


----------------------
--- EFFECT MASKING ---
----------------------

♯_ : ⦃ Δ ∼ Δ₀ ▸ Δ′ ⦄ → Free Δ′ A → Free Δ A
♯_ ⦃ w ⦄ = fold pure (λ op′ k′ → impure (inj▸ᵣ op′) (k′ ∘ proj-ret▸ᵣ ⦃ w ⦄))


