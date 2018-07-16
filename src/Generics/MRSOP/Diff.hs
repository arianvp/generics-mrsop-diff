{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.Diff where

import Control.Applicative
import Control.Monad (guard)
import Data.Proxy
import Data.Type.Equality ((:~:)(Refl), testEquality)
import Generics.MRSOP.Base
import Generics.MRSOP.Base (match)
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper.Deep

data Almu (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> * where
  Peel
    :: (IsNat ix, IsNat iy)
    => Ctxs ki codes ix iy
    -> Ctxs ki codes ix iy
    -> Spine ki codes (Lkup ix codes) -- TODO: is this ix or iy?
    -> Almu ki codes ix

data Spine (ki :: kon -> *) (codes :: [[[Atom kon]]]) (sum :: [[Atom kon]]) :: * where
  Scp :: Spine ki codes sum
  Schg
    :: Constr sum n1
    -> Constr sum n2
    -> Al ki codes (Lkup n1 sum) (Lkup n2 sum)
    -> Spine ki codes sum

npToAl :: NP (At ki codes) xs -> Al ki codes xs xs
npToAl NP0 = A0 NP0 NP0
npToAl (px :* pxs) = AX NP0 NP0 px (npToAl pxs)

sCns ::
     Constr sum n -> NP (At ki codes) (Lkup n sum) -> Spine ki codes sum
sCns c x = Schg c c (npToAl x)

data Al (ki :: kon -> *)  (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  A0
    :: PoA ki (Fix ki codes) p1
    -> PoA ki (Fix ki codes) p2
    -> Al ki codes p1 p2
  AX
    :: PoA ki (Fix ki codes) p1
    -> PoA ki (Fix ki codes) p2
    -> At ki codes a
    -> Al ki codes p1' p2'
    -> Al ki codes (p1 :++: (a ': p1')) (p2 :++: (a ': p2'))

--  Trivial patch on constants is 
data TrivialK (ki :: kon -> *) :: kon -> * where
  Trivial :: ki kon -> ki kon -> TrivialK ki kon
 -- This shouldn't be Fix, but Almu

data At (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Atom kon -> * where
  AtSet :: TrivialK ki kon -> At ki codes (K kon)
  AtFix :: IsNat ix => Almu ki codes ix -> At ki codes (I ix)

applyAt ::
     Eq1 ki
  => At ki codes a
  -> NA ki (Fix ki codes) a
  -> Maybe (NA ki (Fix ki codes) a)
applyAt (AtSet (Trivial k1 k2)) (NA_K k3) = do
  guard $ eq1 k1 k3
  pure $ NA_K k2
applyAt (AtFix almu) (NA_I f) = NA_I <$> applyAlmu almu f

-- TODO not sure yet if this is correct, however it seems correct :)
-- I simply followed the types.
applyAl ::
     Eq1 ki
  => Al ki codes xs ys
  -> PoA ki (Fix ki codes) xs
  -> Maybe (PoA ki (Fix ki codes) ys)
applyAl (A0 NP0 inss) NP0 = Just inss
applyAl (A0 (_ :* dels) inss) (x :* xs) = applyAl (A0 dels inss) xs
applyAl (AX (_ :* dels) inss at al') (x :* xs) =
  applyAl (AX dels inss at al') xs
applyAl (AX NP0 NP0 at al') (x :* xs) = (:*) <$> applyAt at x <*> applyAl al' xs
applyAl (AX NP0 (i :* inss) at al') xs =
  (i :*) <$> applyAl (AX NP0 inss at al') xs

applySpine ::
     Eq1 ki
  => Spine ki codes sum
  -> Rep ki (Fix ki codes) sum
  -> Maybe (Rep ki (Fix ki codes) sum)
applySpine spn r =
  case spn of
    Scp -> pure r
    Schg c1 c2 al ->
      case sop r of
        Tag c3 poa -> do
          x <- testEquality c1 c3
          case x of
            Refl -> inj c2 <$> applyAl al poa


-- | Applies a diff
-- Instead of returning  Nothing here, perhaps we want something better
-- like actually telling why it failed in the future.
--
applyAlmu ::
     Eq1 ki
  => Almu ki codes ix
  -> Fix ki codes ix
  -> Maybe (Fix ki codes ix)
applyAlmu (Peel dels inss spn) f@(Fix x) = do
  y <- removeCtxs dels f
  let (Fix x') = fillCtxs y inss
  Fix <$> applySpine spn x'
  

