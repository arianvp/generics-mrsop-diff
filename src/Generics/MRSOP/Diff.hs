{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.Diff where

import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Base (match)
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper

-- TODO make ctx not use Fam, but Fix
data Almu (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) :: Nat -> * where
  Peel
    :: (IsNat ix, IsNat iy)
    => Proxy iy 
    -> Ctxs ki fam codes ix iy
    -> Ctxs ki fam codes iy ix
    -> Spine ki fam codes (Lkup ix codes)  -- TODO: is this ix or iy?
    -> Almu ki fam codes ix

data Spine (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) (sum :: [[Atom kon]]) :: * where
  Scp :: Spine ki fam codes sum
  Schg
    :: Constr sum n1
    -> Constr sum n2
    -> Al ki fam codes (Lkup n1 sum) (Lkup n2 sum)
    -> Spine ki fam codes sum

npToAl :: NP (At ki fam codes) xs -> Al ki fam codes xs xs
npToAl NP0 = A0 NP0 NP0
npToAl (px :* pxs) = AX NP0 NP0 px (npToAl pxs)

sCns ::
     Constr sum n -> NP (At ki fam codes) (Lkup n sum) -> Spine ki fam codes sum
sCns c x = Schg c c (npToAl x)

data Al (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  A0
    :: PoA ki (Fix ki codes) p1
    -> PoA ki (Fix ki codes) p2
    -> Al ki fam codes p1 p2
  AX
    :: PoA ki (Fix ki codes) p1
    -> PoA ki (Fix ki codes) p2
    -> At ki fam codes a
    -> Al ki fam codes p1' p2'
    -> Al ki fam codes (p1 :++: (a ': p1')) (p2 :++: (a ': p2'))

--  Trivial patch on constants is 
data TrivialK (ki :: kon -> *) :: kon -> * where
  Trivial :: ki kon -> ki kon -> TrivialK ki kon
 -- This shouldn't be Fix, but Almu

data At (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) :: Atom kon -> * where
  AtSet :: TrivialK ki kon -> At ki fam codes (K kon)
  AtFix :: IsNat ix => Almu ki fam codes ix -> At ki fam codes (I ix)
