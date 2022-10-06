module Free.State where

import Free

data State s k = Put s k | Get (s -> k)
  deriving Functor

put :: State s < f => s -> Free f ()
put s = Do $ inj $ Put s $ Pure ()

get :: State s < f => Free f s
get = Do $ inj $ Get Pure


hState :: Functor f => s -> Free (State s + f) a -> Free f (s, a)
hState = flip $ handle_ $ Handler_
  (\ x s -> (s, x))
  (\ op s -> case op of
      (Put s k) -> k s
      (Get k)   -> k s s)

-- hState :: Functor f => s -> Free (State s + f) a -> Free f (a, s)
-- hState s (Pure x) = return (x, s)
-- hState _ (Do (L (Put s k))) = hState s k
-- hState s (Do (L (Get k))) = hState s (k s)
-- hState s (Do (R op)) = Do (fmap (hState s) op)

