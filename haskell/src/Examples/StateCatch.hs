module Examples.StateCatch where

import Hefty
import Free
import Elab
import Algebraic.State
import Algebraic.Abort
import HigherOrder.Except

example :: Hefty (Lift (State Int) ⊕ Except ⊕ Lift Nop) Int
example = do
  lift0 (Put (1 :: Int))
  catch (do lift0 (Put (2 :: Int))
            throw)
        (do (i :: Int) <- lift Get
            lift0 (Put (i + 1)))
  lift Get


testExample :: Maybe (Int, Int)
testExample = un $ hAbort $ hState 0
            $ hfold return (eLift ⊕ eExcept ⊕ eLift)
            $ example
