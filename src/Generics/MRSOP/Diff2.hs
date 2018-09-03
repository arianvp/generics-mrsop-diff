{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.Diff2 where

import Data.Type.Equality
import Control.Monad (guard, (<=<))
import Generics.MRSOP.Base
import Generics.MRSOP.Util

newtype AlmuMin ki codes ix iy = AlmuMin  { unAlmuMin :: Almu ki codes iy ix }

type InsCtx ki codes ix xs = Ctx ki codes (Almu ki codes) ix xs
type DelCtx ki codes ix xs = Ctx ki codes (AlmuMin ki codes) ix xs

data InsOrDel (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: (Nat -> Nat -> *) -> * where
  CtxIns :: InsOrDel ki codes (Almu ki codes)
  CtxDel :: InsOrDel ki codes (AlmuMin ki codes)
  


-- Say we want a stiff diff between
--
--   x = Two (Two a b) (Three x y z)
--
--   y = Three (Two a b) (Three x y z) (Three u w v)

---  Del (Two * (Three x y z))
--            |
--            v
--            Del (Two * a)
--                     |
--                     v
--                     Spn (stiffS)
--


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
    

data Almu (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Nat -> Nat -> * where
  -- | When stuff can't be figured out, we just delete subtree and insert subtree.  Stupid diff is stupid
  -- This might not be the best approach right now, but we can always
  -- later look for an embedding  Fix i -> Fix j -> Almu i j
  Stiff :: (IsNat ix, IsNat iy) => Fix ki codes ix -> Fix ki codes iy -> Almu ki codes ix iy
  Spn
    :: (IsNat ix) 
    => Spine ki codes (Lkup ix codes)
    -> Almu ki codes ix ix
  Ins
    :: Constr (Lkup iy codes) c
    -> InsCtx ki codes ix (Lkup c (Lkup iy codes)) -- its an ix with an iy typed-hoed
    -> Almu ki codes ix iy
  Del
    :: IsNat iy
    => Constr (Lkup ix codes) c
    -> DelCtx ki codes iy (Lkup c (Lkup ix codes))
    -> Almu ki codes ix iy


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
  AtFix :: (IsNat ix) => Almu ki codes ix ix -> At ki codes ('I ix)




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

insCtx
  :: (IsNat ix, Eq1 ki)
  => InsCtx ki codes ix xs
  -> Fix ki codes ix
  -> Maybe (PoA ki (Fix ki codes) xs)
insCtx (H x x2) x1 = (\x -> NA_I x :* x2) <$> applyAlmu x x1
insCtx (T x x2) x1 = (x :*) <$> insCtx x2 x1


delCtx
  :: (Eq1 ki, IsNat ix)
  => DelCtx ki codes ix xs
  -> PoA ki (Fix ki codes) xs
  -> Maybe (Fix ki codes ix)
delCtx (H spu atmus) (NA_I x :* p) = applyAlmu (unAlmuMin spu) x
delCtx (T atmu al) (at :* p) = delCtx al p

applyAlmu ::
     (IsNat ix, Eq1 ki)
  => Almu ki codes ix iy
  -> Fix ki codes ix
  -> Maybe (Fix ki codes iy)
applyAlmu almu f@(Fix x) =
  case almu of
    Spn spine -> Fix <$> applySpine spine x
    Ins c ctx -> Fix . inj c <$> insCtx ctx f
    Del c ctx -> delCtx ctx <=< match c $ x
