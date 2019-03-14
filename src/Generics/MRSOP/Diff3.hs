{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Generics.MRSOP.Diff3 where
  

import Data.List (intersperse)

import Data.Type.Equality (testEquality, (:~:)(Refl))
import Data.Proxy
import Data.Functor.Const
import Control.Monad (guard)
import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Control.Monad ((<=<))

--  Trivial patch on constants is 
data TrivialK (ki :: kon -> *) :: kon -> * where
  Trivial :: ki kon -> ki kon -> TrivialK ki kon

instance Show1 ki => Show (TrivialK ki x) where
  show (Trivial x y) = show1 x ++ "|" ++ show1 y

data At (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Atom kon -> * where
  AtSet :: TrivialK ki kon -> At ki codes ('K kon)
  AtFix :: (IsNat ix) => Almu ki codes ix ix -> At ki codes ('I ix)

instance Show1 ki => Show1 (At ki codes) where
  show1 (AtSet t) = show t
  show1 (AtFix a) = show a
  
data Al (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  A0 :: Al ki codes '[] '[]
  AX :: At ki codes x -> Al ki codes xs ys -> Al ki codes (x ': xs)  (x ': ys)
  ADel :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes (x ': xs) ys
  AIns :: NA ki (Fix ki codes) x -> Al ki codes xs ys -> Al ki codes xs (x ': ys)

instance Show1 ki => Show (Al ki codes xs ys) where
  show A0 = "A0"
  show (AX x xs) = "(AX " ++ show1 x  ++ " " ++ show xs  ++ ")"
  show (ADel x xs) = "(ADel " ++ show x  ++ " " ++ show xs  ++ ")"
  show (AIns x xs) = "(AIns " ++ show x  ++ " " ++ show xs  ++ ")"

newtype AlmuMin ki codes ix iy = AlmuMin  { unAlmuMin :: Almu ki codes iy ix }
  deriving Show 

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

type InsCtx ki codes ix xs = Ctx ki codes (Almu ki codes) ix xs
type DelCtx ki codes ix xs = Ctx ki codes (AlmuMin ki codes) ix xs

instance Show x => Show1 (Const x) where
  show1 (Const x) = show x

instance Show1 ki => Show (InsCtx ki codes ix xs) where
  show (H p poa) = "(H " ++ show p ++ " " ++ show poa ++ ")"
  show (T n c)   = "(T " ++ show n  ++ " " ++ show c ++ ")"
instance Show1 ki => Show (DelCtx ki codes ix xs) where
  show (H p poa) = "(H " ++ show p ++ " " ++ show poa ++ ")"
  show (T n c)   = "(T " ++ show n  ++ " " ++ show c ++ ")"


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

showC :: Constr x y -> String
showC = ('C':) . show . go
  where
    go :: Constr x y -> Int
    go CZ = 0
    go (CS s) = 1 + go s

instance (Show1 ki) => Show (Almu ki codes ix iy) where
  show (Spn s) = "(Spn " ++ show s ++ ")"
  show (Ins c ic) = "(Ins " ++ showC c ++ " " ++ show ic ++ ")"
  show (Del c ic) = "(Del " ++ showC c ++ " " ++ show ic ++ ")"

instance (Show1 p) => Show1 (NP p) where
  show1 np = parens . concat . intersperse " "  $ elimNP show1 np
    where
      parens x = "(" ++ x  ++ ")"

instance (Show1 ki) => Show (Spine ki codes ix iy) where
  show Scp = "COPY"
  show (SCns c x) = "(Scns " ++ showC c ++ " " ++ show1 x ++ ")" 
  show (SChg c1 c2 a) = "(SChg " ++ showC c1  ++ " " ++ showC c2  ++ " " ++ show a  ++ ")"

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

guard' :: String -> Bool -> Either String ()
guard' s False = Left s
guard' _ True  = Right ()

instance Show1 SNat where
  show1 = show . go
    where
     go :: SNat n -> Int
     go SZ = 0
     go (SS s) = 1 + go s

instance Show1 (Constr r) where
  show1 = showC

applyAt
  :: C ki
  => (At ki codes :*: NA ki (Fix ki codes)) a
  -> Either String (NA ki (Fix ki codes) a)
applyAt (AtSet (Trivial a' b) :*: NA_K a)  
  | eq1 a' b  = pure (NA_K a)
  | eq1 a' a  = pure (NA_K b)
  | otherwise = Left "atom"
applyAt (AtFix x :*: NA_I x') = NA_I <$> applyAlmu x x'

applyAl
  :: C ki
  => Al ki codes xs ys
  -> PoA ki (Fix ki codes) xs
  -> Either String (PoA ki (Fix ki codes) ys)
applyAl A0 NP0 = return NP0
applyAl (AX dx dxs) (x :* xs) =
  (:*) <$> applyAt (dx :*: x) <*> applyAl dxs xs
applyAl (AIns x dxs) xs =
  (x :*) <$> applyAl dxs xs 
applyAl (ADel x dxs) (x' :* xs) =
  guard' "al del" (eq1 x x') *> applyAl dxs xs
  -- applyAl dxs xs

testEquality' :: (Show1 f , TestEquality f)
              => f a -> f b -> Either String (a :~: b)
testEquality' x y = case testEquality x y of
  Just r -> Right r
  Nothing -> Left ("te: " ++ show1 x ++ ", " ++ show1 y)

applySpine 
  :: C ki
  => SNat ix
  -> SNat iy
  -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
  -> Rep ki (Fix ki codes) (Lkup ix codes)
  -> Either String (Rep ki (Fix ki codes) (Lkup iy codes))
applySpine _ _ Scp x = return x
applySpine ix iy (SCns c1 dxs) (sop -> Tag c2 xs) =  do
  Refl <- testEquality' ix iy
  Refl <- testEquality' c1 c2
  inj c2 <$> (mapNPM applyAt (zipNP dxs xs))
applySpine _ _ (SChg c1 c2 al) (sop -> Tag c3 xs) = do
  Refl <- testEquality' c1 c3
  inj c2 <$> applyAl al xs

insCtx
  :: (IsNat ix, C ki)
  => InsCtx ki codes ix xs
  -> Fix ki codes ix
  -> Either String (PoA ki (Fix ki codes) xs)
insCtx (H x x2) x1 = (\x -> NA_I x :* x2) <$> applyAlmu x x1
insCtx (T x x2) x1 = (x :*) <$> insCtx x2 x1

delCtx
  :: (C ki, IsNat ix)
  => DelCtx ki codes ix xs
  -> PoA ki (Fix ki codes) xs
  -> Either String (Fix ki codes ix)
delCtx (H spu atmus) (NA_I x :* p) = applyAlmu (unAlmuMin spu) x
delCtx (T atmu al) (at :* p) = delCtx al p

applyAlmu 
  :: forall ki codes ix iy. (IsNat ix, IsNat iy, C ki)
  => Almu ki codes ix iy
  -> Fix ki codes ix
  -> Either String (Fix ki codes iy)
applyAlmu (Spn spine) (AnnFix _ rep) = Fix <$> applySpine (getSNat (Proxy @ix)) (getSNat (Proxy @iy)) spine rep
applyAlmu (Ins c ctx) f@(AnnFix _ rep) = Fix . inj c <$> insCtx ctx f
applyAlmu (Del c ctx) (AnnFix _ rep) = delCtx ctx <=< m2e . match c $ rep
  where
    m2e Nothing  = Left (show "del")
    m2e (Just r) = Right r

type C ki = (Eq1 ki , Show1 ki)

-- it's only disjoint 

-- TODO bit weird. is this correct?
mergeAt :: Eq1 ki => At ki codes a -> At ki codes a -> Maybe (At ki codes a)
mergeAt  (AtSet (Trivial k1 k2)) (AtSet (Trivial k3 k4)) = 
   if k1 `eq1` k2
   then pure $ AtSet $ Trivial k3 k4
   else if k3 `eq1` k4
   then pure $ AtSet $ Trivial k3 k4
   else Nothing
mergeAt (AtFix x) (AtFix y) = AtFix <$> mergeAlmu x y

mergeAtAl :: Eq1 ki => NP (At ki codes) xs -> Al ki codes xs ys -> Maybe (Al ki codes xs ys)
mergeAtAl NP0 A0 = pure A0
-- potential: mergeAtAl [] (AIns at al) = AIns at A0
--            mergeAtAl xs (AIns at al) = AIns at <$> mergeAtAl xs al
mergeAtAl xs (AIns at al) = AIns at <$> mergeAtAl xs al
mergeAtAl (x :* xs) (ADel at al)
  | identityAt x = ADel at <$> mergeAtAl xs al
  | otherwise    = Nothing
mergeAtAl (x :* xs) (AX at al) = AX <$> (mergeAt x at)  <*> mergeAtAl xs al

identityAt :: (Eq1 ki) => At ki codes a -> Bool
identityAt (AtFix (Spn Scp)) = True
identityAt (AtSet (Trivial k1 k2)) = eq1 k1 k2
identityAt _ = False


makeIdAt :: NA ki (Fix ki codes) a -> At ki codes a
makeIdAt (NA_I x) = AtFix (Spn Scp)
makeIdAt (NA_K k) = AtSet (Trivial k k)

mergeAlAt :: Eq1 ki => Al ki codes xs ys -> NP (At ki codes) xs -> Maybe (NP (At ki codes) ys)
mergeAlAt A0 NP0 = pure NP0
mergeAlAt (AIns at al) xs = (makeIdAt at :*) <$> mergeAlAt al xs
mergeAlAt (ADel at al) (x :* xs)
  | identityAt x = mergeAlAt al xs
  | otherwise    = Nothing
mergeAlAt (AX a al)   (x :* xs) = (:*) <$> mergeAt a x <*> mergeAlAt al xs


mergeAts :: Eq1 ki => NP (At ki codes) xs -> NP (At ki codes) xs -> Maybe (NP (At ki codes) xs)
mergeAts NP0 NP0 = pure NP0
mergeAts (x :* xs) (y :* ys) = (:*) <$> mergeAt x y <*> mergeAts xs ys

mergeSpine :: Eq1 ki
           => SNat ix
           -> SNat iy
           -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
           -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
           -> Maybe (Spine ki codes (Lkup ix codes) (Lkup iy codes))
mergeSpine _ _ Scp s = pure s
mergeSpine _ _ s Scp = pure Scp
mergeSpine _ _ (SCns cx xs) (SCns cy ys) = do
  Refl <- testEquality cx cy
  SCns cx <$> mergeAts xs ys
mergeSpine _ _ (SCns cx xs) (SChg cy cz al) = do
  -- this one is nice, because it allows us to change the type
  --
  -- if we have a 
  --
  --  SCNs Add xs   and a SChg Add Asg al
  --
  --  we changed an Expr to a Stmt, but that's okay as long as
  --  we can merge the change in both fields xs and al!!
  --
  Refl <- testEquality cx cy
  SChg cy cz <$> mergeAtAl xs al
mergeSpine ix iy (SChg cx cy al) (SCns cz zs) = do
  -- THIS is the only difference between Multirec and Regular, we can only do this
  -- if within the same family
  Refl <- testEquality ix iy
  Refl <- testEquality cx cz
  SCns cy <$> mergeAlAt al zs
mergeSpine _ _ SChg{} SChg{} = Nothing

mergeCtxAt
 :: forall ki codes ix iy xs. (Eq1 ki, IsNat ix, IsNat iy) 
 => DelCtx ki codes iy xs
 -> NP (At ki codes) xs
 -> Maybe (Almu ki codes ix iy)
mergeCtxAt (H (AlmuMin almu') rest) (AtFix almu :* xs) = do
  -- TODO Very carefully look if this is correct
  Refl <- testEquality (almuDest almu) (almuDest almu')
  x <- mergeAlmu almu' almu
  Refl <- testEquality (almuSrc x) (getSNat (Proxy @ix))
  guard (and $ elimNP identityAt xs)
  pure x
mergeCtxAt (T almu' ctx) (x :* xs) = mergeCtxAt ctx xs

mergeAtCtx :: (Eq1 ki, IsNat iy) => NP (At ki codes) xs -> DelCtx ki codes iy xs -> Maybe (DelCtx ki codes iy xs)
mergeAtCtx (AtFix almu :* xs) (H (AlmuMin almu') rest) = do
  Refl <- testEquality (almuDest almu) (almuDest almu')
  almu'' <- mergeAlmu almu almu'
  guard (and $ elimNP identityAt xs)
  pure $ H  (AlmuMin almu'') rest
mergeAtCtx (x :* xs) (T a  ctx) = do
   T a  <$> mergeAtCtx xs ctx
mergeAtCtx NP0 x = case x of {}

almuDest :: forall ix iy ki codes. IsNat iy => Almu ki codes ix iy -> SNat iy
almuDest _ = getSNat (Proxy @iy)

almuSrc :: forall ix iy ki codes. IsNat ix => Almu ki codes ix iy -> SNat ix
almuSrc _ = getSNat (Proxy @ix)


mergeCtxAlmu :: (Eq1 ki, IsNat ix )
             => InsCtx ki codes ix xs
             -> Almu ki codes ix ix
             -> Maybe (NP (At ki codes) xs)
mergeCtxAlmu (H almu' rest) almu = do 
  -- almu':: exists iy . Almu ix iy
  -- but we need  Almu ix ix
  Refl <- testEquality (almuDest almu) (almuDest almu')
  x <- AtFix <$> mergeAlmu almu' almu
  pure $ x :* mapNP makeIdAt rest
mergeCtxAlmu (T a    ctx) almu = 
  (makeIdAt a :*) <$> mergeCtxAlmu ctx almu

mergeAlmuCtx :: (Eq1 ki, IsNat ix) => Almu ki codes ix ix -> InsCtx ki codes ix xs -> Maybe (InsCtx ki codes ix xs)
mergeAlmuCtx almu (H almu' rest) = do
  Refl <- testEquality (almuDest almu) (almuDest almu')
  almu'' <- mergeAlmu almu almu'
  pure (H almu'' rest)
mergeAlmuCtx almu (T a ctx) = T a <$> mergeAlmuCtx almu ctx

mergeAlmu :: forall ki codes ix iy. (Eq1 ki, IsNat ix, IsNat iy) => Almu ki codes ix iy -> Almu ki codes ix iy -> Maybe (Almu ki codes ix iy)


mergeAlmu Ins{} Ins{} = Nothing
mergeAlmu (Ins c1 s1) (Spn s2) =  do
  -- THIS Note, we can only SCns if they are in the same type inside the family
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Spn . SCns c1 <$> mergeCtxAlmu s1 (Spn s2)
mergeAlmu (Ins c1 s1) (Del c2 s2) = do
  -- THIS Note, we can only SCns if they are in the same type inside the family
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Spn . SCns c1 <$> mergeCtxAlmu s1 (Del c2 s2)
mergeAlmu (Spn s1) (Ins c2 s2) = do
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Ins c2 <$> (mergeAlmuCtx (Spn s1) s2)
mergeAlmu (Del c1 s1) (Ins c2 s2) = do
  Refl <- testEquality (getSNat (Proxy @ix)) (getSNat (Proxy @iy))
  Ins c2 <$> (mergeAlmuCtx (Del c1 s1) s2)

mergeAlmu (Spn s1) (Spn s2) = Spn <$> mergeSpine (getSNat (Proxy @ix)) (getSNat (Proxy @iy)) s1 s2
mergeAlmu (Spn Scp) (Del c2 s2) = pure $ Del c2 s2
mergeAlmu (Spn (SCns c1 at1)) (Del c2 s2) = do
  
  Refl <- testEquality c1 c2
  Del c1 <$> mergeAtCtx at1 s2
mergeAlmu (Spn SChg{}) Del{} = Nothing
mergeAlmu (Del c1 s2) (Spn Scp) = pure $ Spn Scp
mergeAlmu (Del c1 s1) (Spn (SCns c2 at2)) = do
  Refl <- testEquality c1 c2
  mergeCtxAt s1 at2
mergeAlmu Del{} (Spn SChg{}) = Nothing
mergeAlmu Del{} Del{} = Nothing
