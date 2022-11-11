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
un : Free Nil A → A
un (pure x) = x
