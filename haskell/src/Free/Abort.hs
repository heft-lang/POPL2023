module Free.Abort where

import Free

data Abort k = Abort
  deriving Functor

abort :: Abort < f => Free f a
abort = Do $ inj $ Abort

hAbort :: Functor f => Free (Abort + f) a -> Free f (Maybe a)
hAbort = handle $ Handler
  Just
  (\ _ -> return Nothing)

  
