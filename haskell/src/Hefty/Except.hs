module Hefty.Except where

import Free
import Hefty
import Elab
import Algebraic.Abort

data Except f k
  = forall a. Catch (f a) (f a) (a -> k)
  | Throw

deriving instance forall f. Functor (Except f)

instance HFunctor Except where
  hmap f (Catch m1 m2 k) = Catch (f m1) (f m2) k
  hmap _ Throw = Throw

catch :: Except <| h
      => Hefty h a -> Hefty h a -> Hefty h a
catch m1 m2 = Op $ injH $ Catch m1 m2 Return

throw :: ( HFunctor h
         , Except <| h )
      => Hefty h a
throw = Op (injH $ Throw)


-- elaboration into Abort

eExcept :: forall f.
           ( Functor f
           , Abort < f )
        => Elab Except f
eExcept = Alg $ \ x -> case x of
  Catch m1 m2 k -> do
    v <- hup hAbort m1
    case v of
      Just x -> k x
      Nothing -> m2 >>= k
  Throw -> Do $ inj $ Abort

