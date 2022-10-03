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

variable a b c : Level
         A B C P : Set a
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

variable ε ε′ ε″ ε‴ ε₀ ε₁ ε₂ ε₃ : Effect


{-
Effects can be summed by taking their (disjoint) union.
-}

infixr 12 _⊕_
_⊕_ : Effect → Effect → Effect
Op (ε₁ ⊕ ε₂) = Op ε₁ ⊎ Op ε₂
Ret (ε₁ ⊕ ε₂) = [ Ret ε₁ , Ret ε₂ ]


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

data Free (ε : Effect) (A : Set) : Set where
  pure    : A                                      → Free ε A
  impure  : (op : Op ε) (k : Ret ε op → Free ε A)  → Free ε A


{-
The free monad can be folded using the following recursion scheme:
-}

fold : (A → B) → ((op : Op ε) (k : Ret ε op → B) → B) → Free ε A → B
fold gen alg (pure x)       = gen x
fold gen alg (impure op k)  = alg op (fold gen alg ∘ k)


{-
Using `fold`, we can map and bind free monadic computations:
-}
fmap : (A → B) → Free ε A → Free ε B
fmap f = fold (pure ∘ f) impure

_>>=_ : Free ε A → (A → Free ε B) → Free ε B
m >>= g = fold g impure m

_>>_ : Free ε A → Free ε B → Free ε B
m₁ >> m₂ = m₁ >>= λ _ → m₂


{-
Some lemmas about fold and bind:
-}

fold≡ : (m : Free ε A) → fold pure impure m ≡ m
fold≡ (pure x) = refl
fold≡ (impure op k) = cong (impure op) (extensionality (λ x → fold≡ (k x)))

Free-unitₗ-≡ : {x : A} (k : A → Free ε B)
             → pure x >>= k ≡ k x
Free-unitₗ-≡ _ = refl

Free-unitᵣ-≡ : (m : Free ε A)
             → m >>= pure ≡ m
Free-unitᵣ-≡ (pure x) = refl
Free-unitᵣ-≡ (impure op k) = cong (λ x → impure op x) (extensionality $ λ y → Free-unitᵣ-≡ $ k y) 

Free-assoc-≡ : (m : Free ε A) (k₁ : A → Free ε B) (k₂ : B → Free ε C)
             → (m >>= k₁) >>= k₂ ≡ m >>= (λ x → (k₁ x) >>= k₂)
Free-assoc-≡ (pure x) k₁ k₂ = refl
Free-assoc-≡ (impure op k) k₁ k₂ = cong (λ x → impure op x) (extensionality $ λ x → Free-assoc-≡ (k x) k₁ k₂)

Free-cong₂ : (m : Free ε A) (k k' : A → Free ε B)
           → (∀ x → k x ≡ k' x)
           → (m >>= k) ≡ (m >>= k')
Free-cong₂ (pure x) k k' eq = eq _
Free-cong₂ (impure op k₁) k k' eq = cong (λ x → impure op x) $ extensionality $ λ x →
  cong (λ y → (k₁ x) >>= y) $ extensionality eq


----------------------
--- ROW INSERTIONS ---
----------------------

{-
A row insertion witness ε ∼ ε₀ ▸ ε′ is a proof relevant witness that (1) ε is
given by a "row" of summed effects, and (2) ε can be obtained by inserting ε₀
into the row ε′.
-}

data _∼_▸_ : Effect → Effect → Effect → Set₁ where
  insert :                 (ε₀ ⊕ ε′) ∼ ε₀ ▸ ε′
  sift   : (ε ∼ ε₀ ▸ ε′) → ((ε₁ ⊕ ε) ∼ ε₀ ▸ (ε₁ ⊕ ε′))


{-
We add the row insertion witness constructors as instances to allow Agda to
infer row instance witnesses for us.

The two constructors overlap, so proof search using these witnesses is only
useful if we use the Agda flag `--overlapping-instances`.
-}

instance
  insert▸ : (ε₀ ⊕ ε′) ∼ ε₀ ▸ ε′
  insert▸ = insert

  sift▸ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → ((ε₁ ⊕ ε) ∼ ε₀ ▸ (ε₁ ⊕ ε′))
  sift▸ ⦃ w ⦄ = sift w


{-
Some helper functions and lemmas using row insertion witnesses.
-}

inj▸ₗ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Op ε₀  → Op ε
inj▸ᵣ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Op ε′  → Op ε

inj▸ₗ ⦃ insert ⦄  = inj₁
inj▸ₗ ⦃ sift p ⦄  = inj₂ ∘ inj▸ₗ ⦃ p ⦄

inj▸ᵣ ⦃ insert ⦄  = inj₂
inj▸ᵣ ⦃ sift p ⦄  = [ inj₁ , inj₂ ∘ inj▸ᵣ ⦃ p ⦄ ]

proj-ret▸ₗ : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ {op : Op ε₀} → Ret ε (inj▸ₗ op) → Ret ε₀ op
proj-ret▸ₗ ⦃ w = insert ⦄ = id
proj-ret▸ₗ ⦃ w = sift w ⦄ = proj-ret▸ₗ ⦃ w ⦄

proj-ret▸ᵣ : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ {op : Op ε′} → Ret ε (inj▸ᵣ op) → Ret ε′ op
proj-ret▸ᵣ ⦃ w = insert ⦄ = id
proj-ret▸ᵣ ⦃ w = sift w ⦄ {op = inj₁ x} = id
proj-ret▸ᵣ ⦃ w = sift w ⦄ {op = inj₂ y} = proj-ret▸ᵣ ⦃ w ⦄

inj▸ₗ-ret≡ : ⦃ p : ε ∼ ε₀ ▸ ε′ ⦄ (op : Op ε₀)
           → Ret ε (inj▸ₗ op) ≡ Ret ε₀ op
inj▸ₗ-ret≡ ⦃ insert ⦄ _  = refl
inj▸ₗ-ret≡ ⦃ sift p ⦄    = inj▸ₗ-ret≡ ⦃ p ⦄

inj▸ᵣ-ret≡ : ⦃ p : ε ∼ ε₀ ▸ ε′ ⦄ (op : Op ε′)
           → Ret ε (inj▸ᵣ op) ≡ Ret ε′ op
inj▸ᵣ-ret≡ ⦃ insert ⦄ op  = refl
inj▸ᵣ-ret≡ ⦃ sift p ⦄     = [ (λ _ → refl) , inj▸ᵣ-ret≡ ⦃ p ⦄ ]

case▸ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄
      → Op ε
      → (Op ε₀  → B)
      → (Op ε′  → B)
      → B
case▸ ⦃ insert ⦄ x f g = [ f , g ] x
case▸ ⦃ sift p ⦄ x f g = [ g ∘ inj₁ , (λ y → case▸ ⦃ p ⦄ y f (g ∘ inj₂)) ] x

case▸≡ : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄
       → (op : Op ε)
       → ((op′ : Op ε₀) → op ≡ inj▸ₗ op′ → B)
       → ((op′ : Op ε′) → op ≡ inj▸ᵣ op′ → B)
       → B
case▸≡ ⦃ w = insert ⦄ (inj₁ x) f g = f x refl
case▸≡ ⦃ w = insert ⦄ (inj₂ y) f g = g y refl
case▸≡ ⦃ w = sift p ⦄ (inj₁ x) f g = g (inj₁ x) refl
case▸≡ ⦃ w = sift p ⦄ (inj₂ y) f g = case▸≡ ⦃ p ⦄ y (λ op′ → f op′ ∘ cong inj₂) (λ op′ → g (inj₂ op′) ∘ cong inj₂)

to-front : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ → Free ε A → Free (ε₀ ⊕ ε′) A
to-front {ε₀ = ε₀} ⦃ w ⦄ (pure x) = pure x
to-front {ε₀ = ε₀} ⦃ insert ⦄ (impure op k) = impure op (to-front ⦃ insert ⦄ ∘ k)
to-front {ε₀ = ε₀} ⦃ sift w ⦄ (impure (inj₁ op) k) = impure (inj₂ (inj₁ op)) (to-front ⦃ sift w ⦄ ∘ k)
to-front {ε₀ = ε₀} ⦃ sift {ε = ε} {ε′ = ε′} w ⦄ t@(impure (inj₂ op) k) = case▸≡ ⦃ w ⦄ op
  (λ op′ eq →
    impure
      (inj₁ op′)
      ( to-front ⦃ sift w ⦄
      ∘ k
      ∘ subst id (begin
          Ret ε₀ op′
        ≡⟨ sym (inj▸ₗ-ret≡ ⦃ w ⦄ op′) ⟩
          Ret ε (inj▸ₗ ⦃ w ⦄ op′)
        ≡⟨ sym $ cong (Ret ε) eq ⟩
          Ret ε op
        ∎)))
  (λ op′ eq →
    impure (inj₂ (inj₂ op′))
      ( to-front ⦃ sift w ⦄
      ∘ k
      ∘ subst id (begin
          Ret ε′ op′
        ≡⟨ sym (inj▸ᵣ-ret≡ ⦃ w ⦄ op′) ⟩
          Ret ε (inj▸ᵣ ⦃ w ⦄ op′)
        ≡⟨ (sym $ cong (Ret ε) eq) ⟩
          Ret ε op
        ∎)))

from-front : ⦃ w : ε ∼ ε₀ ▸ ε′ ⦄ → Free (ε₀ ⊕ ε′) A → Free ε A
from-front ⦃ w = w ⦄ (pure x) = pure x
from-front ⦃ w = w ⦄ (impure (inj₁ op) k) = impure (inj▸ₗ op) (from-front ∘ k ∘ proj-ret▸ₗ ⦃ w ⦄)
from-front ⦃ w = w ⦄ (impure (inj₂ op) k) = impure (inj▸ᵣ op) (from-front ∘ k ∘ proj-ret▸ᵣ ⦃ w ⦄)


----------------
--- HANDLERS ---
----------------

record ParameterizedHandler (ε : Effect) (P : Set) (G : Set → Set) : Set₁ where
  field
    ret : {A : Set} → A → P → G A
    hdl : {A : Set} (op : Op ε) (k : Ret ε op → P → Free ε′ (G A)) → P → Free ε′ (G A)

open ParameterizedHandler public

handle : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → ParameterizedHandler ε₀ P G → Free ε A → P → Free ε′ (G A)
handle h  =  fold (λ p → pure ∘ ret h p) [ hdl h , (λ op′ k′ → impure op′ ∘ flip k′) ]
             ∘ to-front

record SimpleHandler (ε : Effect) (G : Set → Set) : Set₁ where
  field  ret : ∀ {A} → A → G A
         hdl : ∀ {A} → (op : Op ε) (k : Ret ε op → Free ε′ (G A)) → Free ε′ (G A)

open SimpleHandler public

Simple-to-Parameterized :  SimpleHandler ε G → ParameterizedHandler ε ⊤ G
ret (Simple-to-Parameterized S) x _    = ret S x
hdl (Simple-to-Parameterized S) op k _ = hdl S op (flip k tt)

handle₀ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → SimpleHandler ε₀ G → Free ε A → Free ε′ (G A)
handle₀ SH = flip (handle (Simple-to-Parameterized SH)) tt


----------------------
--- EFFECT MASKING ---
----------------------

♯_ : ⦃ ε ∼ ε₀ ▸ ε′ ⦄ → Free ε′ A → Free ε A
♯_ ⦃ w ⦄ = fold pure (λ op′ k′ → impure (inj▸ᵣ op′) (k′ ∘ proj-ret▸ᵣ ⦃ w ⦄))


