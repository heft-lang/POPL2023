module Elab where

import Free
import Hefty

type Elab h f = Alg h (Free f)


newtype Lift f (h :: * -> *) k = Lift (f k)
  deriving Functor

instance Functor f => HFunctor (Lift f) where
  hmap _ (Lift x) = Lift x

eLift :: ( f < g ) => Elab (Lift f) g
eLift = Alg $ \ x -> case x of
  Lift x -> Do $ inj x

lift0 :: forall f h.
         ( HFunctor h
         , Lift f <| h )
      => (Hefty h () -> f (Hefty h ())) -> Hefty h ()
lift0 f = Op $ injH $ Lift $ f (return ())

lift :: ( HFunctor h
        , Lift f <| h )
     => ((a -> Hefty h a) -> f (Hefty h a)) -> Hefty h a
lift f = Op $ injH $ Lift $ f return
