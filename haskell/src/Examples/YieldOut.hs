module Examples.YieldOut where

import Prelude hiding (or)
import Free
import Free.Yield
import Free.Out
import Free.NonDet

example :: ( Functor f
           , Interleavable (YieldTac + Out + f) )
        => Free (YieldTac + Out + f) ()
example = do
  fork (do out "foo"
           out "bar"
           out "baz") $
    fork (do out "he"
             fork (do out "llo"
                      out "world") $ do
               out "roic") $ do
      out "cha"
      out "chi"

example0 :: ( Functor f
            , Interleavable (YieldTac + Out + f) )
         => Free (YieldTac + Out + f) ()
example0 = do
  fork
    (fork
       (atomic (do out "1.1"; out "1.2"; out "1.3")
               (do out "2.1"; out "2.2"; out "2.3"))
       (out "3"))
    (out "4")

instance Interleavable (YieldTac + Out + Tactic + Nop) where
  isYield (L _) = True
  isYield _ = False
  
  isInterleavable (R (L (Out _ _))) = True
  isInterleavable (L (R (R (R (L (Atomic _)))))) = True
  isInterleavable _ = False
  
testExample :: [String]
testExample =
  map fst $ un $ hTactic $ hOut $ hTacticAll Nothing $ example0

