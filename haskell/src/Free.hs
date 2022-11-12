module Free where

import Control.Monad

data Free f a
  = Pure a
  | Do (f (Free f a))

instance Functor f => Applicative (Free f) where pure = Pure; (<*>) = ap
instance Functor f => Functor (Free f) where fmap = liftM
instance Functor f => Monad (Free f) where
  Pure x >>= k = k x
  Do f >>= k = Do (fmap ((=<<) k) f)


-- functor sum

infixr 6 +
data (f + g) a = L (f a) | R (g a)
  deriving Functor

sum_ :: (f a -> b)
     -> (g a -> b)
     -> (f + g) a -> b
sum_ f _ (L x) = f x
sum_ _ g (R x) = g x


-- functor composition

infixr 6 <>
data (f <> g) a = C { unC :: f (g a) }

deriving instance ( forall a. Show a => Show (f a)
                  , forall a. Show a => Show (g a)
                  , Show a ) => Show ((f <> g) a)


-- natural transformations

newtype f :->: g = Λ { nt :: forall a. f a -> g a }

o :: (g :->: h) -> (f :->: g) -> (f :->: h)
o f2 f1 = Λ $ nt f2 . nt f1


-- isomorphisms

data Iso f g = Iso { to :: f :->: g, from :: g :->: f }

type f <~> g = Iso f g

(<~>) = Iso

isoRefl :: f <~> f
isoRefl = Λ id <~> Λ id

isoSym :: f <~> g -> g <~> f
isoSym iso = from iso <~> to iso

isoTrans :: f <~> g -> g <~> h -> f <~> h
isoTrans iso1 iso2 = (to iso2 `o` to iso1) <~> (from iso1 `o` from iso2)

isoSumCong :: g <~> h -> (f + g) <~> (f + h)
isoSumCong iso = Λ (sum_ L (R . nt (to iso))) <~> Λ (sum_ L (R . nt (from iso)))

isoSumSwap :: (f + (g + h)) <~> (g + (f + h))
isoSumSwap = Λ (sum_ (R . L) (sum_ L (R . R)))
             <~> Λ (sum_ (R . L) (sum_ L (R . R)))


-- injection/toFore pack,
-- which existentially packages `h` and a witness that `g <~> f + h`
data Forephism f g =
  forall h. Functor h => Forephism { forephism :: g <~> (f + h) }


-- functor subsumption

infixr 5 <
class f < g where
  witness :: Forephism f g

-- short-hand

inj :: forall f g a. f < g => f a -> g a
inj x = case witness @f @g of Forephism iso -> nt (from iso) $ L x

proj :: forall f g a. f < g => g a -> Maybe (f a)
proj x = case witness @f @g of
  Forephism iso -> sum_ Just (const Nothing) $ nt (to iso) x

-- sum instances

instance f < f where
  witness = Forephism (Λ L <~> Λ (sum_ id (\ (x :: Nop k) -> case x of)))

instance Functor g => f < (f + g) where
  witness = Forephism isoRefl

instance (Functor h, f < g) => f < h + g where
  witness = case witness @f @g of
    Forephism iso ->
      Forephism (isoTrans (isoSumCong iso) isoSumSwap)


-- id functor

data Id a = Id { unId :: a } deriving ( Functor , Eq )

deriving instance Show a => Show (Id a)


-- ubiquitous "no effect" (used as final row entry)

data Nop k
  deriving Functor

un :: Free Nop a -> a
un (Pure x) = x
un (Do f) = case f of


-- folding trees, paramorphically

parafold :: Functor f
         => (a -> b)
         -> (f (Free f a, b) -> b)
         -> Free f a
         -> b
parafold gen _   (Pure a) = gen a
parafold gen alg (Do f) = alg (fmap (\ x -> (x, parafold gen alg x)) f)

-- folding trees, catamorphically

fold :: Functor f
     => (a -> b)
     -> (f b -> b)
     -> Free f a
     -> b
fold gen alg = parafold gen (alg . fmap snd)


-- simple handler

data Handler f f' g a
  = Handler { ret :: forall b. b -> g b
            , hdl :: f (Free f' (g a)) -> Free f' (g a) }

handle :: ( Functor f
          , Functor f' )
       => Handler f f' g a
       -> Free (f + f') a
       -> Free f' (g a)
handle h = fold (return . ret h) (sum_ (hdl h) Do)


-- parameterized handler

data Handler_ f f' p g a
  = Handler_ { ret_ :: forall b. b -> p -> g b
             , hdl_ :: f (p -> Free f' (g a)) -> p -> Free f' (g a) }

handle_ :: ( Functor f
           , Functor f' )
        => Handler_ f f' p g a
        -> Free (f + f') a
        -> p
        -> Free f' (g a)
handle_ h = fold (fmap return . ret_ h)
                 (sum_ (hdl_ h) (\ x p -> Do $ app p <$> x))
  where app p f = f p


-- paramorphic simple handler

data ParaHandler f f' g a
  = ParaHandler { pararet :: a -> Free f' (g a)
                , parahdl :: f ( Free (f + f') a
                               , Free f' (g a) ) -> Free f' (g a) }

parahandle :: ( Functor f
              , Functor f' )
           => ParaHandler f f' g a
           -> Free (f + f') a
           -> Free f' (g a)
parahandle h = parafold (pararet h) (sum_ (parahdl h) (Do . fmap snd))


-- paramorphic parameterized handler

data ParaHandler_ f f' p g a
  = ParaHandler_ { pararet_ :: a -> p -> Free f' (g a)
                 , parahdl_ :: f ( Free (f + f') a
                                 , p -> Free f' (g a)) -> p -> Free f' (g a) }

parahandle_ :: ( Functor f
           , Functor f' )
        => ParaHandler_ f f' p g a
        -> Free (f + f') a
        -> p
        -> Free f' (g a)
parahandle_ h = parafold (pararet_ h)
                         (sum_ (parahdl_ h) (\ x p -> Do $ fmap (app p . snd) x))
  where app p f = f p


-- convert a tree using a natural transformation

convert :: ( Functor f
           , Functor g )
        => (f :->: g)
        -> Free f a -> Free g a
convert g = fold return (Do . nt g)


-- effect masking

mask :: ( Functor f
        , Functor g )
     => Free g a -> Free (f + g) a
mask = fold return (Do . R)


-- apply a handler and mask that the effect was handled

hup :: forall f g m a.
       ( Functor f
       , Functor g
       , f < g )
    => (forall h. Functor h => Free (f + h) a -> Free h (m a))
    -> Free g a -> Free g (m a)
hup h = case witness @f @g of
  Forephism iso -> convert (from iso) . mask . h . convert (to iso)


-- apply an identity function modulo an insertion witness

hid :: forall f g a.
       ( Functor f
       , Functor g
       , f < g )
    => (forall h. Functor h => Free (f + h) a -> Free (f + h) a)
    -> Free g a -> Free g a
hid h = case witness @f @g of
  Forephism iso -> convert (from iso) . h . convert (to iso)


-- free algebra

data FreeAlg f a 
  = FreeAlg { freeAlg :: f a -> a }

infixr 7 +~
(+~) :: FreeAlg f1 a -> FreeAlg f2 a -> FreeAlg (f1 + f2) a
a1 +~ a2 = FreeAlg $ \ f -> case f of
  L f1 -> freeAlg a1 f1
  R f2 -> freeAlg a2 f2
