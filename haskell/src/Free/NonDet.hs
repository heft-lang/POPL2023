module Free.NonDet where

import Free
import Free.Abort

data NonDet k = Or (Bool -> k)
  deriving Functor

or :: NonDet < f => Free f a -> Free f a -> Free f a
or m1 m2 = Do $ inj $ Or $ \ b -> if b then m1 else m2

hNonDet :: Functor f => Free (NonDet + f) a -> Free f [a]
hNonDet = handle $ Handler
  (\ x -> [x])
  (\ (Or k) -> do
      xs <- k True
      ys <- k False
      return (xs ++ ys))


type Tactic = NonDet + Abort + Nop

falso :: Tactic < f => Free f a
falso = Do $ inj @Tactic $ R $ L $ Abort

disj :: Tactic < f => Free f a -> Free f a -> Free f a
disj m1 m2 = Do $ inj @Tactic $ L $ Or $ \ b -> if b then m1 else m2

hTactic :: Functor f => Free (Tactic + f) a -> Free f [a]
hTactic = handle $ Handler
  (\ x -> [x])
  (\ x -> case x of
      L (Or k) -> do
        xs <- k True
        ys <- k False
        return (xs ++ ys)
      R (L Abort) -> return []
      R (R op) -> case op of)
