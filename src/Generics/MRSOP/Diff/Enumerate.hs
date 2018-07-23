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

-- |
-- Given something of type 'iy'
--
-- and we delete at the root the  Context  'iy -> ix'
-- and then insert at the new root  a Context 'iy -> ix'
-- We get back and 'iy'
--
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
-- TODO: Decide with Victor how to enumerate Ctxs
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
           (Tag c1 p1, Tag c2 p2) -> do
             al <- diffAl p1 p2
             pure $ Schg c1 c2 al

diffAt ::
     (Eq1 ki, MonadPlus m)
  => NA ki (Fix ki codes) a
  -> NA ki (Fix ki codes) a
  -> m (At ki codes a)
diffAt (NA_K k1) (NA_K k2) = pure . AtSet $ Trivial k1 k2
diffAt (NA_I i1) (NA_I i2) = AtFix <$> diffAlmu i1 i2

diffAl ::
     (Eq1 ki, MonadPlus m)
  => PoA ki (Fix ki codes) xs
  -> PoA ki (Fix ki codes) ys
  -> m (Al ki codes xs ys)
diffAl NP0 NP0 = pure $ A0 NP0 NP0
diffAl NP0 bs = undefined
diffAl as NP0 = undefined
diffAl (a :* as) (b :* bs) = undefined
    

diffAlmu ::
     (Eq1 ki, IsNat ix, MonadPlus m)
  => Fix ki codes ix
  -> Fix ki codes ix
  -> m (Almu ki codes ix)
diffAlmu a b = do
  Loc (Fix a') (Fix b') dels inss <- diffCtxs a b
  a'' <- diffSpine a' b'
  pure $ Peel dels inss a''
