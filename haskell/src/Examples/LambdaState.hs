module Examples.LambdaState where

import Hefty
import Free
import Elab
import Free.State
import Hefty.Lambda

example :: forall fun c.
           Hefty (Lambda c fun ⊕ Lift (State Int) ⊕ Lift Nop) Int
example = do
  lift0 (Put (1 :: Int))
  (f :: fun (c Int) Int) <- lambda (\ (x :: c Int) -> do
                                       n1 <- var @fun x
                                       n2 <- var @fun x
                                       return $ n1 + n2)
  apply f incr
  where
    incr = do (n :: Int) <- lift Get; lift0 (Put $ n + 1); lift Get

testExampleCBV :: Int
testExampleCBV =
  fst $ un $ hState 0
      $ hfold @(Free (State Int + Nop)) return (eLambdaCBV ⊕ eLift ⊕ eLift)
      $ example
-- = 4

testExampleCBN :: Int
testExampleCBN =
  fst $ un $ hState 0
      $ hfold @(Free (State Int + Nop)) return (eLambdaCBN ⊕ eLift ⊕ eLift)
      $ example
-- = 5
