module Hefty.Nil where

open import Free
open import Free.Nil
open import Hefty
open import Hefty.Lift


eNil : Elaboration (Lift Nil) ε
alg eNil ()


{-
Automatable elaboration
-}

instance
  eNil′ : Elab (Lift Nil) ε
  orate eNil′ = eNil

