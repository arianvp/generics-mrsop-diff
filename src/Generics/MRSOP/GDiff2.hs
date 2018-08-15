{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.GDiff2 where

import Control.Monad
import Data.Proxy
import Data.Semigroup
import Data.Type.Equality
import Generics.MRSOP.Base
import Generics.MRSOP.Base.Metadata
import Generics.MRSOP.GDiff.Util
import Generics.MRSOP.Util

data SinglCof
  = CofI Nat
         Nat -- type index and constructor index within the type
  | CofK

data Cof (ki :: kon -> *) (codes :: [[[Atom kon]]]) (a :: Atom kon) (c :: SinglCof) where
  ConstrI
    :: (IsNat c, IsNat n)
    => Constr (Lkup n codes) c
    -> Cof ki codes (I n) (CofI n c)
  ConstrK :: ki k -> Cof ki codes (K k) CofK

cofWitnessI :: Cof ki codes (I n) (CofI n c) -> Proxy n
cofWitnessI _ = Proxy

heqCof ::
     (Eq1 ki, TestEquality ki)
  => Cof ki codes a cx
  -> Cof ki codes b cy
  -> Maybe (a :~: b, cx :~: cy)
heqCof cx@(ConstrI x) cy@(ConstrI y) =
  case testEquality (getSNat (cofWitnessI cx)) (getSNat (cofWitnessI cy)) of
    Nothing -> Nothing
    Just Refl ->
      case testEquality x y of
        Nothing -> Nothing
        Just Refl -> Just (Refl, Refl)
heqCof (ConstrK x) (ConstrK y) =
  case testEquality x y of
    Just Refl ->
      if eq1 x y
        then Just (Refl, Refl)
        else Nothing
    Nothing -> Nothing
heqCof _ _ = Nothing

injCof ::
     Cof ki codes a c
  -> PoA ki (Fix ki codes) (Tyof codes c)
  -> NA ki (Fix ki codes) a
injCof (ConstrI c) xs = NA_I (Fix $ inj c xs)
injCof (ConstrK k) xs = NA_K k

matchCof ::
     (Eq1 ki)
  => Cof ki codes a c
  -> NA ki (Fix ki codes) a
  -> Maybe (PoA ki (Fix ki codes) (Tyof codes c))
matchCof (ConstrI c1) (NA_I (Fix x)) = match c1 x
matchCof (ConstrK k) (NA_K k2) = guard (eq1 k k2) >> Just NP0

type family Tyof (codes :: [[[Atom kon]]]) (c :: SinglCof) :: [Atom kon]
  -- we wanted Lkup c . Lkup ix but haskell complains
  -- jTyof (f ': codes) (CofI Z      c) = Lkup c f
  -- Tyof (f ': codes) (CofI (S ix) c) = Tyof codes (CofI ix c)
 where
  Tyof codes (CofI ix c) = Lkup c (Lkup ix codes)
  Tyof codes CofK = '[]

-- {-# INLINE cost #-}
--
--  IDEA: Instead of calculating cost every time (Expensive)
--  build up cost by construction (We get it for free)
cost :: ES ki codes txs tys -> Int
cost ES0 = 0
cost (Ins k c es) = k
cost (Del k c es) = k
cost (Cpy k c es) = k

-- {-# INLINE meet #-}
meet :: ES ki codes txs tys -> ES ki codes txs tys -> ES ki codes txs tys
meet d1 d2 =
  if cost d1 <= cost d2
    then d1
    else d2

data ES (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  ES0 :: ES ki codes '[] '[]
  Ins
    :: Int
    -> Cof ki codes a c
    -> ES ki codes i (Tyof codes c :++: j)
    -> ES ki codes i (a ': j)
  Del
    :: Int
    -> Cof ki codes a c
    -> ES ki codes (Tyof codes c :++: i) j
    -> ES ki codes (a ': i) j
  Cpy
    :: Int
    -> Cof ki codes a c
    -> ES ki codes (Tyof codes c :++: i) (Tyof codes c :++: j)
    -> ES ki codes (a ': i) (a ': j)

data EST (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES ki codes '[] '[] -> EST ki codes '[] '[]
  NC
    :: Cof ki codes y c
    -> ES ki codes '[] (y ': tys)
    -> EST ki codes '[] (Tyof codes c :++: tys)
    -> EST ki codes '[] (y ': tys)
  CN
    :: Cof ki codes x c
    -> ES ki codes (x ': txs) '[]
    -> EST ki codes (Tyof codes c :++: txs) '[]
    -> EST ki codes (x ': txs) '[]
  CC
    :: Cof ki codes x cx
    -> Cof ki codes y cy
    -> ES ki codes (x ': txs) (y ': tys)
    -> EST ki codes (x ': txs) (Tyof codes cy :++: tys)
    -> EST ki codes (Tyof codes cx :++: txs) (y ': tys)
    -> EST ki codes (Tyof codes cx :++: txs) (Tyof codes cy :++: tys)
    -> EST ki codes (x ': txs) (y ': tys)

getDiff :: EST ki codes rxs rys -> ES ki codes rxs rys
getDiff (NN x) = x
getDiff (NC _ x _) = x
getDiff (CN _ x _) = x
getDiff (CC _ _ x _ _ _) = x

extendi ::
     (Eq1 ki, TestEquality ki)
  => Cof ki codes x cx
  -> EST ki codes (Tyof codes cx :++: xs) ys
  -> EST ki codes (x ': xs) ys
extendi cx dt@(NN d) = CN cx (Del (1 + cost d) cx d) dt
extendi cx dt@(CN _ d _) = CN cx (Del (1 + cost d) cx d) dt
extendi cx dt@(NC cy _ dt') =
  let i = extendi cx dt'
      d = dt
      c = dt'
   in CC cx cy (bestDiffT cx cy i d c) i d c
extendi cx dt@(CC _ cy _ dt' _ _) =
  let i = extendi cx dt'
      d = dt
      c = dt'
   in CC cx cy (bestDiffT cx cy i d c) i d c

extendd ::
     (Eq1 ki, TestEquality ki)
  => Cof ki codes y cy
  -> EST ki codes xs (Tyof codes cy :++: ys)
  -> EST ki codes xs (y ': ys)
extendd cy dt@(NN d) = NC cy (Ins (1 + cost d) cy d) dt
extendd cy dt@(NC _ d _) = NC cy (Ins (1 + cost d) cy d) dt
extendd cy dt@(CN cx _ dt') =
  let i = dt
      d = extendd cy dt'
      c = dt'
   in CC cx cy (bestDiffT cx cy i d c) i d c
extendd cy dt@(CC cx _ _ _ dt' _) =
  let i = dt
      d = extendd cy dt'
      c = dt'
   in CC cx cy (bestDiffT cx cy i d c) i d c

bestDiffT ::
     (Eq1 ki, TestEquality ki)
  => Cof ki codes x cx
  -> Cof ki codes y cy
  -> EST ki codes (x ': xs) (Tyof codes cy :++: ys)
  -> EST ki codes (Tyof codes cx :++: xs) (y ': ys)
  -> EST ki codes (Tyof codes cx :++: xs) (Tyof codes cy :++: ys)
  -> ES ki codes (x ': xs) (y ': ys)
bestDiffT cx cy i d c =
  case heqCof cx cy of
    Just (Refl, Refl) ->
      let c' = getDiff c
       in Cpy (cost c') cx c'
    Nothing ->
      let i' = getDiff i
          d' = getDiff d
       in meet (Ins (1 + cost i') cy i') (Del (1 + cost d') cx d')

-- TODO : There is quite a bit of code duplication, but not
-- sure yet how to get rid of it.
diffT ::
     (Eq1 ki, TestEquality ki)
  => PoA ki (Fix ki codes) xs
  -> PoA ki (Fix ki codes) ys
  -> EST ki codes xs ys
diffT NP0 NP0 = NN ES0
diffT (NA_K k :* xs) NP0 =
  let d = diffT xs NP0
      d' = getDiff d
   in CN (ConstrK k) (Del (1 + cost d') (ConstrK k) d') d
diffT (NA_I (Fix rep) :* xs) NP0 =
  case sop rep of
    Tag c poa ->
      let d = diffT (appendNP poa xs) NP0
          d' = getDiff d
       in CN (ConstrI c) (Del (1 + cost d') (ConstrI c) d') d
diffT NP0 (NA_K k :* ys) =
  let d = diffT NP0 ys
      d' = getDiff d
   in NC (ConstrK k) (Ins (1 + cost d') (ConstrK k) d') d
diffT NP0 (NA_I (Fix rep) :* ys) =
  case sop rep of
    Tag c poa ->
      let d = diffT NP0 (appendNP poa ys)
          d' = getDiff d
       in NC (ConstrI c) (Ins (1 + cost d') (ConstrI c) d') d
diffT (NA_I (Fix r1) :* xs) (NA_I (Fix r2) :* ys) =
  case (sop r1, sop r2) of
    (Tag c1 poa1, Tag c2 poa2) ->
      let c = diffT (appendNP poa1 xs) (appendNP poa2 ys)
          cx = ConstrI c1
          cy = ConstrI c2
          i = extendi cx c
          d = extendd cy c
       in CC cx cy (bestDiffT cx cy i d c) i d c
diffT (NA_K k1 :* xs) (NA_I (Fix r2) :* ys) =
  case sop r2 of
    Tag c2 poa2 ->
      let c = diffT xs (appendNP poa2 ys)
          cx = ConstrK k1
          cy = ConstrI c2
          i = extendi cx c
          d = extendd cy c
       in CC cx cy (bestDiffT cx cy i d c) i d c
diffT (NA_I (Fix r1) :* xs) (NA_K k2 :* ys) =
  case sop r1 of
    Tag c1 poa1 ->
      let c = diffT (appendNP poa1 xs) ys
          cx = ConstrI c1
          cy = ConstrK k2
          i = extendi cx c
          d = extendd cy c
       in CC cx cy (bestDiffT cx cy i d c) i d c
diffT (NA_K k1 :* xs) (NA_K k2 :* ys) =
  let c = diffT xs ys
      cx = ConstrK k1
      cy = ConstrK k2
      i = extendi cx c
      d = extendd cy c
   in CC cx cy (bestDiffT cx cy i d c) i d c

diff ::
     forall fam ki codes ix1 ix2 ty1 ty2.
     ( Family ki fam codes
     , ix1 ~ Idx ty1 fam
     , ix2 ~ Idx ty2 fam
     , Lkup ix1 fam ~ ty1
     , Lkup ix2 fam ~ ty2
     , IsNat ix1
     , IsNat ix2
     , Eq1 ki
     , TestEquality ki
     )
  => ty1
  -> ty2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff a b = diff' (deep a) (deep b)

diff' ::
     (Eq1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff' a b = getDiff $ diff'' a b

diff'' ::
     (Eq1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> EST ki codes '[ 'I ix1] '[ 'I ix2]
diff'' x y =
  let x' = NA_I x
      y' = NA_I y
   in diffA x' y'

diffA ::
     (Eq1 ki, TestEquality ki)
  => NA ki (Fix ki codes) x
  -> NA ki (Fix ki codes) y
  -> EST ki codes '[ x] '[ y]
diffA a b = diffPoA (a :* NP0) (b :* NP0)

diffPoA ::
     (Eq1 ki, TestEquality ki)
  => PoA ki (Fix ki codes) '[ x]
  -> PoA ki (Fix ki codes) '[ y]
  -> EST ki codes '[ x] '[ y]
diffPoA = diffT

