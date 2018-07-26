{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.Diff2 where

import Control.Applicative
import Control.Monad (guard)
import Data.Proxy
import Data.Type.Equality ((:~:)(Refl), testEquality)
import Generics.MRSOP.Base
import Generics.MRSOP.Base (match)
import Generics.MRSOP.Util

data Ctx (ki :: kon -> *) (codes :: [[[Atom kon]]]) (ix :: Nat) :: [Atom kon] -> * where
  Here :: Almu ki codes ix -> Ctx ki codes ix ('I ix ': xs)
  There
    :: NA ki (Fix ki codes) a -> Ctx ki codes ix xs -> Ctx ki codes ix (a ': xs)

data Almu (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> * where
  Spn :: (IsNat ix) => Spine ki codes (Lkup ix codes) -> Almu ki codes ix
  Ins
    :: Constr (Lkup ix codes) c
    -> Ctx ki codes ix (Lkup c (Lkup ix codes))
    -> Almu ki codes ix
  Del
    :: Constr (Lkup ix codes) c
    -> Ctx ki codes ix (Lkup c (Lkup ix codes))
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

sCns :: Constr sum n -> NP (At ki codes) (Lkup n sum) -> Spine ki codes sum
sCns c x = Schg c c (npToAl x)

data Al (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  A0
    :: PoA ki (Fix ki codes) p1 -> PoA ki (Fix ki codes) p2 -> Al ki codes p1 p2
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
