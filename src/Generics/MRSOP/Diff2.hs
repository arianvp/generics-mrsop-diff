{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.Diff2 where

import Generics.MRSOP.Base
import Generics.MRSOP.Util

data Ctx (ki :: kon -> *) (codes :: [[[Atom kon]]]) (ix :: Nat) :: [Atom kon] -> * where
  H :: Almu ki codes ix -> PoA ki (Fix ki codes) xs -> Ctx ki codes ix ('I ix ': xs)
  T
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


-- So the problem is, that his mapping is forgetful
--      Al ki codes xs xs 
--      doesnt have a unique representation
--
--      In the Agda code, we have a separate case for Schg and sCns
--
--      and now during merging, we have to recover again the fact
--
--      that we  know that an sCns can only contain  an    NP (At ki codes) xs
sCns :: Constr sum n -> NP (At ki codes) (Lkup n sum) -> Spine ki codes sum
sCns c x = Schg c c (npToAl x)

-- | Old style alignments, which can be trivially lifted to 'Al'
-- but easier to build up
data AlOld (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  OA0 :: AlOld ki codes '[] '[]
  OADel ::  NA ki (Fix ki codes) x -> AlOld ki codes xs ys -> AlOld ki codes (x ': xs) ys
  OAIns ::  NA ki (Fix ki codes) x -> AlOld ki codes xs ys -> AlOld ki codes xs (x ': ys)
  OAX :: At ki codes x -> AlOld ki codes xs ys -> AlOld ki codes (x ': xs) (x ': ys)

nIns :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes xs (x ': ys)
nIns a (A0 d i) = A0 d (a :* i)
nIns a (AX d i x al) = AX d (a :* i) x al

nDel :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes (x ': xs) ys
nDel a (A0 d i) = A0 (a :* d) i
nDel a (AX d i x al) = AX (a :* d) i x al



denormalizeAl :: Al ki codes xs ys -> AlOld ki codes xs ys
denormalizeAl xs =
  case xs of
    A0 NP0 NP0 -> OA0
    A0 NP0 (i :* inss) -> OAIns i (denormalizeAl (A0 NP0 inss))
    A0 (d :* dels) inss -> OADel d (denormalizeAl (A0 dels inss))
    AX NP0 NP0 at al -> OAX at (denormalizeAl al)
    AX NP0 (i :* inss) at al -> OAIns i (denormalizeAl (AX NP0 inss at al))
    AX (d :* dels) inss at al -> OADel d (denormalizeAl (AX dels inss at al))
    
    
normalizeAl :: AlOld ki codes xs ys -> Al ki codes xs ys
normalizeAl xs =
  case xs of
    OA0 -> A0 NP0 NP0
    OAIns a al -> nIns a (normalizeAl al)
    OADel a al -> nDel a (normalizeAl al)
    OAX at al -> AX NP0 NP0 at (normalizeAl al)

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
  AtSet :: TrivialK ki kon -> At ki codes ('K kon)
  AtFix :: IsNat ix => Almu ki codes ix -> At ki codes ('I ix)



