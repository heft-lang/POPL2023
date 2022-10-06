module All where


{- Code corresponding to Section 2 of the paper -}

open import Free

open import Free.Nil
open import Free.State
open import Free.Throw
open import Free.Choice

open import Example.Free.State
open import Example.Free.Choice+State


{- Code corresponding to Section 3 of the paper -}

open import Hefty

open import Hefty.Nil
open import Hefty.Lift
open import Hefty.Catch

open import Example.Hefty.Catch+Throw+State -- also contains material for 5.2


{- Code corresponding to Section 4 of the paper -}

open import Law.Hefty.Catch


{- Code corresponding to Section 5 of the paper -}

{- 5.1: Lambda as a Higher-Order Effect -}

open import Hefty.Lambda

open import Example.Hefty.Lambda+State

{- 5.2: Optionally Transactional Exception Catching
        (see also Example.Hefty.Catch+Throw+State) -}

open import Free.SubJump

{- 5.3: Logic Programming -}

open import Free.Disj

open import Hefty.Once

open import Example.Hefty.Disj+Once

{- 5.4: Concurrency -}

open import Free.Interleave
open import Free.Out

open import Hefty.Concur

open import Example.Hefty.Out+Concur



