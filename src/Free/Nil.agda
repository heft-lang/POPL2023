module Free.Nil where

open import Data.Empty

open import Free

{-
The empty effect
-}

Nil : Effect
Op   Nil = ⊥
Ret  Nil = ⊥-elim


{-
Handling the empty effect
-}
end : Free Nil A → A
end (pure x) = x
