{-# OPTIONS --overlapping-instances --instance-search-depth=10 #-}

module Law.Hefty.Catch where

open import Function
open import Data.Empty
open import Level renaming (zero to ℓ0) using ()
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Sum
open import Data.Universe renaming (Universe to Univ)
private Universe = Univ ℓ0 ℓ0
open Univ ⦃ ... ⦄ renaming (U to T; El to ⟦_⟧)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Postulate.Extensionality

open import Free  hiding (_>>=_; _>>_)
open import Free.Throw

open import Hefty hiding (_>>=_; _>>_)
open import Hefty.Lift
open import Hefty.Catch

{-
An interface of a monad M with:
- A throw and catch operations
- A `run` function that runs a computation, yielding a result `R A` for some `R : Set → Set`
- Laws for bind and throw
- A law that ≡ is a congruence for catc
-}

record CatchIntf
         (M : Set → Set)
         (return : ∀ {A} → A → M A)
         (_>>=_  : ∀ {A B} → M A → (A → M B) → M B)
         : Set₁ where
  field  ⦃ u ⦄  : Universe
         𝑡ℎ𝑟𝑜𝑤   : {t : T} → M ⟦ t ⟧
         𝑐𝑎𝑡𝑐ℎ   : {t : T} → M ⟦ t ⟧ → M ⟦ t ⟧ → M ⟦ t ⟧
         R       : Set → Set
         run     : M A → R A
         bind-throw  : {t₁ t₂ : T} (k : ⟦ t₁ ⟧ → M ⟦ t₁ ⟧)
           → run (𝑡ℎ𝑟𝑜𝑤 >>= k) ≡ run 𝑡ℎ𝑟𝑜𝑤
         catch-return  : {t : T} (x : ⟦ t ⟧) (m : M ⟦ t ⟧)
           → run (𝑐𝑎𝑡𝑐ℎ (return x) m) ≡ run (return x)
         catch-throw₁  : {t : T} (m : M ⟦ t ⟧)
           → run (𝑐𝑎𝑡𝑐ℎ 𝑡ℎ𝑟𝑜𝑤 m) ≡ run m
         catch-throw₂  : {t : T} (m : M ⟦ t ⟧)
           → run (𝑐𝑎𝑡𝑐ℎ m 𝑡ℎ𝑟𝑜𝑤) ≡ run m
         catch-cong    : {t : T} (m₁ m₁′ m₂ m₂′ : M ⟦ t ⟧)
           → run m₁ ≡ run m₁′
           → run m₂ ≡ run m₂′
           → run (𝑐𝑎𝑡𝑐ℎ m₁ m₂) ≡ run (𝑐𝑎𝑡𝑐ℎ m₁′ m₂′)

open CatchIntf

{-
The catch operation and its elaboration in `Hefty.Catch` is a lawful instance of
this interface.
-}

module _ {H : Effectᴴ} {ε : Effect} (E : Elaboration H (Throw ⊕ ε)) where

  private
    h : ∀ {A} ⦃ u : Universe ⦄
        → Free (Throw ⊕ ε) A → Free ε (Maybe A)
    h = handle₀ hThrow

    e : ∀ {A} ⦃ u : Universe ⦄
        → Hefty (Lift Throw ∔ Catch ∔ H) A → Free (Throw ⊕ ε) A
    e = elaborate (eLift ⋎ eCatch ⋎ E)

  CatchImpl₀ : ⦃ u : Universe ⦄
             → CatchIntf (Hefty (Lift Throw ∔ Catch ∔ H)) pure Hefty._>>=_
  u    (CatchImpl₀ ⦃ u ⦄)    = u
  𝑡ℎ𝑟𝑜𝑤 CatchImpl₀            = ‵throwᴴ
  𝑐𝑎𝑡𝑐ℎ CatchImpl₀            = ‵catch
  R    CatchImpl₀            = Free ε ∘ Maybe 
  run  CatchImpl₀            = h ∘ e
  bind-throw    CatchImpl₀  k    = refl
  catch-return  CatchImpl₀  x m  = refl
  catch-throw₁  CatchImpl₀  m    = begin
      h (e (‵catch ‵throwᴴ m))
    ≡⟨ refl ⟩
      h ((♯ h (e ‵throwᴴ)) >>= maybe pure ((e m) >>= pure))
    ≡⟨ cong (λ ■ → h ((♯ h (e ‵throwᴴ)) >>= maybe pure ■)) (Free-unitᵣ-≡ (e m)) ⟩
      h (e m)
    ∎
    where open import Free using (_>>=_)
  catch-throw₂  CatchImpl₀  m    = begin
      h (e (‵catch m ‵throwᴴ))
    ≡⟨ refl ⟩
      h ((♯ h (e m)) >>= maybe pure ((e ‵throwᴴ) >>= pure))
    ≡⟨ cong (λ P → h ((♯ h (e m)) >>= P))
         (extensionality (λ x →
           cong (λ P → maybe pure P x)
             (trans  (Free-unitᵣ-≡ (e ‵throwᴴ))
                     (cong (impure (inj₁ throw))
                       (extensionality (λ x → ⊥-elim x)))))) ⟩
      h ((♯ h (e m)) >>= maybe pure ‵throw)
    ≡⟨ catch-throw-lem (e m) ⟩
      h (e m) ∎
    where
      open import Free using (_>>=_)
      
      catch-throw-lem : (m : Free (Throw ⊕ _) A)
                      → h ((♯ h m) >>= maybe pure ‵throw)
                        ≡ handle₀ hThrow m
      catch-throw-lem (pure x)                = refl
      catch-throw-lem (impure (inj₁ throw) k) = refl
      catch-throw-lem (impure (inj₂ y) k) = cong (impure y) (extensionality (λ x → catch-throw-lem (k x)))
  catch-cong CatchImpl₀ m₁ m₁' m₂ m₂' eq₁ eq₂ = begin
      h (e (‵catch m₁ m₂))
    ≡⟨ refl ⟩
       h ((♯ h (e m₁)) >>=ᶠ maybe pure (e m₂ >>=ᶠ pure))
    ≡⟨ cong
         (λ P → h ((♯ h (e m₁)) >>=ᶠ P))
         (extensionality (λ x → cong (λ P → maybe pure P x) (Free-unitᵣ-≡ (e m₂)))) ⟩
       h ((♯ h (e m₁)) >>=ᶠ maybe pure (e m₂))
    ≡⟨ cong (λ P → h ((♯ P) >>=ᶠ maybe pure (e m₂))) eq₁ ⟩
       h ((♯ h (e m₁')) >>=ᶠ maybe pure (e m₂))
    ≡⟨ hThrow-bind-distr (♯ h (e m₁')) _ ⟩
       (h (♯ h (e m₁'))) >>=ᶠ maybe (h ∘ maybe pure (e m₂)) (pure nothing)
    ≡⟨ cong
         (λ P → (h (♯ (h (e m₁')))) >>=ᶠ maybe P (pure nothing))
         (extensionality (λ x → maybe-distr x pure (e m₂) h)) ⟩
       (h (♯ h (e m₁'))) >>=ᶠ maybe (maybe (h ∘ pure) (h (e m₂))) (pure nothing)
    ≡⟨ cong
         (λ P → (h (♯ (h (e m₁')))) >>=ᶠ maybe (maybe (h ∘ pure) P) (pure nothing))
         eq₂ ⟩
       (h (♯ h (e m₁'))) >>=ᶠ maybe (maybe (h ∘ pure) (h (e m₂'))) (pure nothing)
    ≡⟨ cong
         (λ P → (h (♯ (h (e m₁')))) >>=ᶠ maybe P (pure nothing))
         (extensionality (λ x → sym $ maybe-distr x pure (e m₂') h)) ⟩
       (h (♯ h (e m₁'))) >>=ᶠ maybe (h ∘ maybe pure (e m₂')) (pure nothing)
    ≡⟨ (sym $ hThrow-bind-distr (♯ h (e m₁')) _) ⟩
       h ((♯ h (e m₁')) >>=ᶠ maybe pure (e m₂'))
    ≡⟨ cong
         (λ P → h ((♯ h (e m₁')) >>=ᶠ P))
         (extensionality (λ x →
           cong
             (λ P → maybe pure P x)
             (sym $ Free-unitᵣ-≡ (e m₂')))) ⟩
      h ((♯ h (e m₁')) >>=ᶠ maybe pure (e m₂' >>=ᶠ pure))
    ≡⟨ refl ⟩
      h (e (‵catch m₁' m₂')) ∎
   where
     open import Hefty renaming (_>>=_ to _>>=ᴴ_) using ()
     open import Free renaming (_>>=_ to _>>=ᶠ_) using ()
     
     maybe-distr : (x : Maybe A)
                   {B : Maybe A → Set}
                   (f : (a : A) → B (just a))
                   (b : B nothing)
                   (g : ∀ {x : Maybe A} → B x → C)
                 → g {x = x} (maybe {B = B} f b x) ≡ maybe (g ∘ f) (g b) x
     maybe-distr (just x) f b g = refl
     maybe-distr nothing  f b g = refl

     hThrow-bind-distr : (m : Free (Throw ⊕ ε) A) (k : A → Free (Throw ⊕ ε) B)
                       → handle₀ hThrow (m >>=ᶠ k) ≡ (handle₀ hThrow m) >>=ᶠ maybe (handle₀ hThrow ∘ k) (pure nothing)
     hThrow-bind-distr (pure x) k = refl
     hThrow-bind-distr (impure (inj₁ throw) k₁) k = refl
     hThrow-bind-distr (impure (inj₂ y) k₁) k = cong (impure y) (extensionality (λ x → hThrow-bind-distr (k₁ x) k))


{-
The usual, non-modular, abbreviation of catch is also lawful
-}

catchᴬ : ⦃ w : ε ∼ Throw ▸ ε′ ⦄ → Free ε A → Free ε A → Free ε A
catchᴬ m₁ m₂ = (♯ (handle₀ hThrow m₁)) >>= (maybe pure m₂)
  where open import Free using (_>>=_)

module _ {ε : Effect} where

  open import Free using (_>>=_)

  h : ∀ {A} → Free (Throw ⊕ ε) A → Free ε (Maybe A)
  h = handle₀ hThrow

  CatchImpl₁  : ⦃ u : Universe ⦄
              →  CatchIntf (Free (Throw ⊕ ε)) pure _>>=_
  u    (CatchImpl₁ ⦃ u ⦄) = u
  𝑡ℎ𝑟𝑜𝑤 CatchImpl₁         = ‵throw
  𝑐𝑎𝑡𝑐ℎ CatchImpl₁         = catchᴬ
  R    CatchImpl₁         = Free ε ∘ Maybe
  run  CatchImpl₁         = h
  bind-throw    CatchImpl₁ k   = refl
  catch-return  CatchImpl₁ x m = refl
  catch-throw₁  CatchImpl₁ m   = refl
  catch-throw₂  CatchImpl₁ m    = begin
      h (catchᴬ m ‵throw)
    ≡⟨ refl ⟩
      h ((♯ h m) >>= maybe pure ‵throw)
    ≡⟨ catch-throw-lem m ⟩
      h m ∎
    where
      catch-throw-lem : (m : Free (Throw ⊕ ε) A)
                      → h ((♯ h m) >>= maybe pure ‵throw)
                        ≡ handle₀ hThrow m
      catch-throw-lem (pure x) = refl
      catch-throw-lem (impure (inj₁ throw) k) = refl
      catch-throw-lem (impure (inj₂ y) k) = cong (impure y) (extensionality (λ x → catch-throw-lem (k x)))
  catch-cong CatchImpl₁ m₁ m₁′ m₂ m₂′ eq₁ eq₂ = begin
      h (catchᴬ m₁ m₂)
    ≡⟨ refl ⟩
      h ((♯ (h m₁)) >>= maybe pure m₂)
    ≡⟨ cong (λ P → h ((♯ P) >>= maybe pure m₂)) eq₁ ⟩
      h ((♯ h m₁′) >>= maybe pure m₂)
    ≡⟨ h-distr (♯ h m₁′) (maybe pure m₂) ⟩
      (h (♯ h m₁′)) >>= maybe (h ∘ maybe pure m₂) (pure nothing)
    ≡⟨ cong (λ P → (h (♯ h m₁′)) >>= P)
         (extensionality (λ x →
           cong (λ P → maybe P (pure nothing) x)
             (extensionality (λ x →
               maybe-distr x pure m₂ h)))) ⟩
      (h (♯ h m₁′)) >>= maybe (maybe (h ∘ pure) (h m₂)) (pure nothing)
    ≡⟨ cong (λ P → (h (♯ h m₁′)) >>= P)
         (extensionality (λ x →
           cong (λ P → maybe P (pure nothing) x)
             (extensionality (λ x →
               cong (λ P → maybe _ P x) eq₂)))) ⟩
      (h (♯ h m₁′)) >>= maybe (maybe (h ∘ pure) (h m₂′)) (pure nothing)
    ≡⟨ ( sym
       $ cong (λ P → (h (♯ h m₁′)) >>= P)
           (extensionality (λ x →
             cong (λ P → maybe P (pure nothing) x)
               (extensionality (λ x →
                 maybe-distr x pure m₂′ h))))) ⟩
      (h (♯ h m₁′)) >>= maybe (h ∘ maybe pure m₂′) (pure nothing)
    ≡⟨ (sym $ h-distr (♯ h m₁′) (maybe pure m₂′)) ⟩
      h ((♯ h m₁′) >>= maybe pure m₂′)
    ≡⟨ refl ⟩
      h (catchᴬ m₁′ m₂′) ∎
    where
      maybe-distr : (x : Maybe A)
                    {B : Maybe A → Set}
                    (f : (a : A) → B (just a))
                    (b : B nothing)
                    (g : ∀ {x : Maybe A} → B x → C)
                  → g {x = x} (maybe {B = B} f b x) ≡ maybe (g ∘ f) (g b) x
      maybe-distr (just x) f b g = refl
      maybe-distr nothing f b g = refl

      h-distr : (m : Free (Throw ⊕ ε) A) (k : A → Free (Throw ⊕ ε) B)
              → h (m >>= k) ≡ (h m) >>= maybe (h ∘ k) (pure nothing)
      h-distr (pure x) k = refl
      h-distr (impure (inj₁ throw) k₁) k = refl
      h-distr (impure (inj₂ y) k₁) k = cong (impure y) (extensionality (λ x → h-distr (k₁ x) k))

