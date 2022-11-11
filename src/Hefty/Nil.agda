module Hefty.Nil where

open import Free
open import Free.Nil
open import Hefty
open import Hefty.Lift


eNil : Elaboration (Lift Nil) Δ
alg eNil ()


{-
Automatable elaboration
-}

instance
  eNil′ : Elab (Lift Nil) Δ
  orate eNil′ = eNil

