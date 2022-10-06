module Hefty where

import Control.Monad

data Hefty h a
  = Return a
  | Op (h (Hefty h) (Hefty h a))

class (forall f. Functor (h f)) => HFunctor h where
  hmap :: (forall a. f a -> g a) -> h f a -> h g a


instance HFunctor h => Applicative (Hefty h) where pure = Return; (<*>) = ap
instance HFunctor h => Functor (Hefty h) where fmap = liftM
instance HFunctor h => Monad (Hefty h) where
  Return x >>= k = k x
  Op f     >>= k = Op (fmap ((=<<) k) f)

-- hfunctor sum

infixr 6 ⊕
data (h1 ⊕ h2) (f :: * -> *) a = LH (h1 f a) | RH (h2 f a)
  deriving Functor

-- hfunctor subsumption

class (h1 :: (* -> *) -> (* -> *)) <| h2 where
  injH  :: h1 f a -> h2 f a
  projH :: h2 f a -> Maybe (h1 f a)

instance h <| h where
  injH = id
  projH = Just

instance h1 <| (h1 ⊕ h2) where
  injH    = LH
  projH x = case x of LH x -> Just x; RH _ -> Nothing

instance h1 <| h3 => h1 <| (h2 ⊕ h3) where
  injH    = RH . injH
  projH (LH _) = Nothing
  projH (RH x) = projH x

instance (HFunctor h1, HFunctor h2) => HFunctor (h1 ⊕ h2) where
  hmap f (LH x) = LH $ hmap f x
  hmap f (RH x) = RH $ hmap f x

data Alg h g = Alg { alg :: forall a. h g (g a) -> g a }

hfold :: forall g h a.
         HFunctor h
      => (forall a. a -> g a)
      -> Alg h g
      -> Hefty h a
      -> g a
hfold gen _   (Return a) = gen a
hfold gen a (Op f)   = alg a $ hmap (hfold gen a) (fmap (hfold gen a) f)

(⊕) :: Alg h1 g -> Alg h2 g -> Alg (h1 ⊕ h2) g
a1 ⊕ a2 = Alg $ \ x -> case x of
  LH x -> alg a1 x
  RH x -> alg a2 x

