{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

-- | Non-deterministic enumeraiton of patches
module Generics.MRSOP.Diff.Enumerate where

import Control.Monad
import Data.Proxy
import Data.Type.Equality
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.Util hiding (Cons, Nil)
import Generics.MRSOP.Zipper.Deep

data Loc (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> * where
  Loc
    :: IsNat ix
    => Fix ki codes iy
    -> Fix ki codes iy
    -> Ctxs ki codes iy ix
    -> Ctxs ki codes iy ix
    -> Loc ki codes iy

-- | Enumerate arbitrary insertions and deletions such that we 
-- can turn Fix a into Fix a.  
diffCtxs ::
     (Eq1 ki, IsNat ix, MonadPlus m)
  => Fix ki codes ix
  -> Fix ki codes ix
  -> m (Loc ki codes ix)
diffCtxs a b = pure (Loc a b Nil Nil)

-- so sure, the spine is pure, if we have a trivial alignment
-- and then later do the other stuff. But we
-- just inline thr
diffSpine ::
     (MonadPlus m, Eq1 ki)
  => Rep ki (Fix ki codes) s
  -> Rep ki (Fix ki codes) s
  -> m (Spine ki codes s)
diffSpine s1 s2 =
  if eq1 s1 s2
    then pure Scp
    else case (sop s1, sop s2) of
           (Tag c1 p1, Tag c2 p2) -> pure $ Schg c1 c2 _

diffAlmu ::
     (Eq1 ki, IsNat ix, MonadPlus m)
  => Fix ki codes ix
  -> Fix ki codes ix
  -> m (Almu ki codes ix)
diffAlmu a b = do
  Loc (Fix a') (Fix b') dels inss <- diffCtxs a b
  a'' <- diffSpine a' b'
  pure $ Peel dels inss a''
