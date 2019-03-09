{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module Generics.MRSOP.Diff3 where
  
import Data.Type.Equality (testEquality, (:~:)(Refl))

import Control.Monad (guard)
import Generics.MRSOP.Base
import Generics.MRSOP.Util

--  Trivial patch on constants is 
data TrivialK (ki :: kon -> *) :: kon -> * where
  Trivial :: ki kon -> ki kon -> TrivialK ki kon

data At (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Atom kon -> * where
  AtSet :: TrivialK ki kon -> At ki codes ('K kon)
  AtFix :: (IsNat ix) => Almu ki codes ix ix -> At ki codes ('I ix)
  
data Al (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  A0 :: Al ki codes '[] '[]
  AX :: At ki codes x -> Al ki codes xs ys -> Al ki codes (x ': xs)  (x ': ys)
  ADel :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes (x ': xs) ys
  AIns :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes xs (x ': ys)

newtype AlmuMin ki codes ix iy = AlmuMin  { unAlmuMin :: Almu ki codes iy ix }


-- | An NP p xs, but there exists an x in xs such that h x
--
-- Note that:  NP p xs <=> Ctx' p p xs
--
-- and that the list is never empty, because it contains at
-- least the pointed element
--
data InsOrDel (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: (Nat -> Nat -> *) -> * where
  CtxIns :: InsOrDel ki codes (Almu ki codes)
  CtxDel :: InsOrDel ki codes (AlmuMin ki codes)


data Ctx (ki :: kon -> *)
         (codes :: [[[Atom kon]]]) 
         (p :: Nat -> Nat -> *)
         (ix :: Nat) :: [Atom kon] -> * where
  H :: IsNat iy
    => p ix iy
    -> PoA ki (Fix ki codes) xs
    -> Ctx ki codes p ix ('I iy ': xs)
  T :: NA ki (Fix ki codes) a
    -> Ctx ki codes p ix xs
    -> Ctx ki codes p ix (a ': xs)
--
--
{-
data Ctx (h :: x -> *) (p :: x -> *) :: [x] -> * where
  H :: h x -> NP p xs -> Ctx h p (x ': xs)
  T :: p x -> Ctx h p xs -> Ctx h p (x ': xs)

ctxIsNP :: Ctx p p xs -> NP p xs
ctxIsNP (H p xs) = p :* xs
ctxIsNP (T p xs) = p :* ctxIsNP xs

npIsCtx :: NP p (x ': xs) -> Ctx p p (x ': xs)
npIsCtx (p :* xs) = H p xs
-}

type InsCtx ki codes ix xs = Ctx ki codes (Almu ki codes) ix xs
type DelCtx ki codes ix xs = Ctx ki codes (AlmuMin ki codes) ix xs

data Almu (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> Nat -> * where
  Spn :: Spine ki codes (Lkup ix codes) (Lkup iy codes) -> Almu ki codes ix iy
  Ins
    :: Constr (Lkup iy codes) c
    -> InsCtx ki codes ix (Lkup c (Lkup iy codes)) -- its an ix with an iy typed-hoed
    -> Almu ki codes ix iy
  Del
    :: IsNat iy
    => Constr (Lkup ix codes) c
    -> DelCtx ki codes iy (Lkup c (Lkup ix codes))
    -> Almu ki codes ix iy
  -- TODO ins del
      

-- OR what about:  ix iy
data Spine (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [[Atom kon]] -> [[Atom kon]] -> * where
  Scp :: Spine ki codes s1 s1
  SCns 
    :: Constr s1 c1 
    -> NP (At ki codes) (Lkup c1 s1)
    -> Spine ki codes s1 s2
  SChg
    :: Constr s1 c1
    -> Constr s2 c2
    -> Al ki codes (Lkup c1 s1) (Lkup c2 s2)
    -> Spine ki codes s1 s2


applyAt
  :: Eq1 ki
  => (At ki codes :*: NA ki (Fix ki codes)) a
  -> Maybe (NA ki (Fix ki codes) a)
applyAt (AtSet (Trivial a' b) :*: NA_K a) = 
  guard (a `eq1` a') *> pure (NA_K b)
applyAt (AtFix x :*: NA_I x') = NA_I <$> applyAlmu x x'

applyAl
  :: Eq1 ki
  => Al ki codes xs ys
  -> PoA ki (Fix ki codes) xs
  -> Maybe (PoA ki (Fix ki codes) ys)
applyAl A0 NP0 = Just NP0
applyAl (AX dx dxs) (x :* xs) =
  (:*) <$> applyAt (dx :*: x) <*> applyAl dxs xs
applyAl (AIns x dxs) xs =
  (x :*) <$> applyAl dxs xs 
applyAl (ADel x dxs) (x' :* xs) =
  guard (eq1 x x') *> applyAl dxs xs


applySpine 
  :: Eq1 ki
  => Spine ki codes s1 s2
  -> Rep ki (Fix ki codes) s1
  -> Maybe (Rep ki (Fix ki codes) s2)
applySpine Scp x = Just x
applySpine (SCns c1 dxs) (sop -> Tag c2 xs) =  do
  undefined
  {- -- TODO check whether they are over the same sum
  Refl <- testEquality c1 c2
  inj c2 <$> (mapNPM applyAt (zipNP dxs xs)) -}
applySpine (SChg c1 c2 al) (sop -> Tag c3 xs) = do
  Refl <- testEquality c1 c3
  inj c2 <$> applyAl al xs



applyAlmu 
  :: Eq1 ki 
  => Almu ki codes ix iy
  -> Fix ki codes ix
  -> Maybe (Fix ki codes iy)
applyAlmu (Spn spine) (Fix rep) = Fix <$> applySpine spine rep

