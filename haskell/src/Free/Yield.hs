module Free.Yield where

import Prelude hiding (or)
import Free
import Free.NonDet as ND
import Free.Abort

data Yield k = Yield k
  deriving Functor


-- inserts yields as every other operation

interleave :: ( Functor f
              , Functor g )
           => Free ((Yield + NonDet + g) + f) a -> Free ((Yield + NonDet + g) + f) a
interleave = interl False -- only start yielding after second operation
  where
    interl _     (Pure x)    = return x
    interl b     (Do (L op)) = Do $ L $ fmap (interl b) op
    interl False (Do (R op)) = Do $ R $ fmap (interl True) op
    interl True  (Do (R op)) = Do $ L $ L $ Yield $ Do $ R $ fmap (interl True) op


-- round-robin

hRR :: Functor f
    => [Free ((Yield + NonDet + Nop) + f) a]
    -> Free ((Yield + NonDet + Nop) + f) a
    -> Free f [a]
hRR = flip $ parahandle_ $ ParaHandler_
  (\ x q -> if null q
    then return [x]
    else do r <- hRR (tail q) (head q); return (x:r))
  (\ op q -> case op of
      L (Yield (k, k')) -> if null q
        then k' q
        else hRR (tail q++[k]) (head q)
      R (L (Or k)) -> snd (k True) $ q++[fst $ k False]
      R (R op) -> case op of)


-- atomic block

data Atomic k = Atomic (Bool -> k) -- first branch is the atomic block; second branch is the continuation
  deriving Functor


-- round-robin for threads that yield

type YieldTac = Yield + NonDet + Abort + Atomic + Nop

-- kill a thread

kill :: YieldTac < f => Free f a
kill = Do $ inj @YieldTac $ R $ R $ L $ Abort

-- fork an interleaving thread that is killed upon completion

fork :: ( Functor f
        , Interleavable f
        , YieldTac < f )
     => Free f ()
     -> Free f a
     -> Free f a
fork m1 m2 =
  Do $ inj @YieldTac $ R $ L $ Or (\ b -> if b
                                    then (do interleave1 m1; kill)
                                    else (interleave1 m2))

-- atomic block

atomic :: ( Functor f
          , Interleavable f
          , YieldTac < f )
       => Free f ()
       -> Free f a
       -> Free f a
atomic m1 c =
  Do $ inj @YieldTac $ R $ R $ R $ L
     $ Atomic (\ b -> if b
                then (do m1; kill)
                else (interleave1 c))

-- choice between two threads

choose :: ( Functor f
          , YieldTac < f )
       => Free f a
       -> Free f a
       -> Free f a
choose m1 m2 =
  Do $ inj @YieldTac $ R $ L $ Or (\ b -> if b then m1 else m2)


-- hTacticRR :: Functor f
--           => [Free (YieldTac + f) a]
--           -> Free (YieldTac + f) a
--           -> Free f [a]
-- hTacticRR = flip $ parahandle_ $ ParaHandler_
--   (\ x q -> if null q
--     then return [x]
--     else do r <- hTacticRR (tail q) (head q); return (x:r))
--   (\ op q -> case op of
--       L (Yield (k, k')) -> yield q k k'
--       R (L (Or k)) -> snd (k True) $ q++[fst $ k False]
--       R (R (L Abort)) -> if null q
--         then return []
--         else hTacticRR (tail q) (head q)
--       R (R (R op)) -> case op of)
--   where
--     yield []    _ k' = k' []
--     yield (m:q) k _  = hTacticRR (q++[k]) m


class Interleavable f where
  isYield         :: f k -> Bool
  isInterleavable :: f k -> Bool

interleave1 :: ( Functor f
               , Interleavable f
               , YieldTac < f )
            => Free f a -> Free f a
interleave1 = interl1 False -- only start yielding after second operation
  where
    interl1 _     (Pure x)    = return x
    interl1 _     (Do op) | isYield op = Do op
    interl1 False (Do op) = if isInterleavable op
      then Do $ fmap (interl1 True)  op
      else Do $ fmap (interl1 False) op
    interl1 True  (Do op) = if isInterleavable op
      then hid @YieldTac (Do . L . L . Yield) $ Do op
      else Do $ fmap (interl1 True) op


hTacticAll :: forall f a.
              ( Functor f
              , Interleavable (YieldTac + f)
              , Tactic < f
              , Ord a )
           => Maybe (Free (YieldTac + f) a)
           -> Free (YieldTac + f) a
           -> Free f (Maybe a)
hTacticAll = flip $ parahandle_ $ ParaHandler_
  (\ x q -> case q of
      Nothing -> return $ Just x
      Just m  -> do y <- hTacticAll Nothing m; return (max y (Just x)))
  (\ op q -> case op of
      L (Yield (k, _))         -> yield q (interleave1 k)
      R (L (Or k))             -> run2 q (k True) (k False)
      R (R (L Abort))          -> stop q
      R (R (R (L (Atomic k)))) -> run2 q (k True) (k False)
      R (R (R (R op)))         -> case op of)
  where
    yield Nothing  k = hTacticAll Nothing k
    yield (Just m) k = disj (hTacticAll (Just k) m) (hTacticAll (Just m) k)

    stop Nothing = return Nothing
    stop (Just m) = hTacticAll Nothing m

    run2 Nothing  (k1, k1') (k2, k2') = (k1' $ Just k2) `disj` (k2' $ Just k1)
    run2 (Just m) (k1, k1') (k2, k2') = (k1' $ Just $ choose k2 m)
                                        `disj`
                                        (k2' $ Just $ choose k1 m)
    

