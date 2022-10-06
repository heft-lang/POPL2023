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

{- Both S3 and S5.2 -}
open import Example.Hefty.Catch+Throw+State


{- Code corresponding to Section 4 of the paper -}

open import Law.Hefty.Catch


{- Code corresponding to Section 5 of the paper -}

{- 5.1 -}
open import Hefty.Lambda

open import Example.Hefty.Lambda+State

{- 5.2: See also Example.Hefty.Catch+Throw+State -}

open import Free.SubJump
