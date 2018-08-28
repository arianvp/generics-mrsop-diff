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

module Generics.MRSOP.GDiff where

import Debug.Trace
import GHC.Exts hiding (IsList)

import Control.Monad
import Data.Proxy
import Data.Functor.Const
import Data.Semigroup
import Data.Type.Equality
import Generics.MRSOP.Base hiding (listPrfNP)
import Generics.MRSOP.Base.Metadata
import Generics.MRSOP.GDiff.Util
import Generics.MRSOP.Util (Nat, Eq1(eq1), IsNat, (:++:), Lkup, Show1(show1), Idx, El(El), getSNat)

import Data.Digems.Generic.Digest (Digest, Digestible1)
import qualified Data.Digems.Generic.Digest as Digest
import qualified Generics.MRSOP.AG as AG

data SinglCof
  = CofI Nat
         Nat -- type index and constructor index within the type
  | CofK


-- | Tests if two trees are equal, based on their annotated hash
hashEq
  :: (TestEquality ki, Digestible1 ki, Eq1 ki) 
  => NA ki (AnnFix ki codes (Const Digest)) a
  -> NA ki (AnnFix ki codes (Const Digest)) b
  -> Maybe (a :~: b)
hashEq (NA_I x) (NA_I y) =
  case testEquality (sNatFixIdx x) (sNatFixIdx y) of
    Just Refl | getAnn x == getAnn y -> Just Refl
    _ -> Nothing
hashEq (NA_K x) (NA_K y) =
  case testEquality x y of
    Just Refl | eq1 x y -> Just Refl
    _ -> Nothing 
hashEq _ _ = Nothing

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

type family Tyof (codes :: [[[Atom kon]]]) (c :: SinglCof) :: [Atom kon]
  -- we wanted Lkup c . Lkup ix but haskell complains
  -- jTyof (f ': codes) (CofI Z      c) = Lkup c f
  -- Tyof (f ': codes) (CofI (S ix) c) = Tyof codes (CofI ix c)
 where
  Tyof codes (CofI ix c) = Lkup c (Lkup ix codes)
  Tyof codes CofK = '[]

data ES (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  ES0 :: ES ki codes '[] '[]
  Ins
    :: ListPrf j
    -> ListPrf (Tyof codes c)
    -> Int
    -> Cof ki codes a c
    -> ES ki codes i (Tyof codes c :++: j)
    -> ES ki codes i (a ': j)
  Del
    :: ListPrf i
    -> ListPrf (Tyof codes c)
    -> Int
    -> Cof ki codes a c
    -> ES ki codes (Tyof codes c :++: i) j
    -> ES ki codes (a ': i) j
  Cpy
    :: ListPrf i
    -> ListPrf j
    -> ListPrf (Tyof codes c)
    -> Int
    -> Cof ki codes a c
    -> ES ki codes (Tyof codes c :++: i) (Tyof codes c :++: j)
    -> ES ki codes (a ': i) (a ': j)

-- When Showing, we do not know what the family that we're showing is,
-- as edit scripts are not parameterised over the family.
-- hence, we can not get the datatype info
showCof ::
     (HasDatatypeInfo ki fam codes, Show1 ki) => Cof ki codes a c -> String
showCof (ConstrK k) = show1 k
showCof (ConstrI c) = show c

instance (HasDatatypeInfo ki fam codes, Show1 ki) =>
         Show (ES ki codes xs ys) where
  show ES0 = "ES0"
  show (Ins _ _ _ c d) = "Ins " ++ showCof c ++ " $ " ++ show d
  show (Del _ _ _ c d) = "Del " ++ showCof c ++ " $ " ++ show d
  show (Cpy _ _ _ _ c d) = "Cpy " ++ showCof c ++ " $ " ++ show d

-- Smart constructors 
-- TODO this is incorrect. I should only pass  ListPrf (Tyof codes c) and ListPrf j
ins ::
     ListPrf j
  -> ListPrf (Tyof codes c)
  -> Int
  -> Cof ki codes a c
  -> ES ki codes i (Tyof codes c :++: j)
  -> ES ki codes i (a ': j)
ins = Ins

del ::
     ListPrf i
  -> ListPrf (Tyof codes c)
  -> Int
  -> Cof ki codes a c
  -> ES ki codes (Tyof codes c :++: i) j
  -> ES ki codes (a ': i) j
del = Del

cpy ::
     ListPrf i
  -> ListPrf j
  -> ListPrf (Tyof codes c)
  -> Int
  -> Cof ki codes a c
  -> ES ki codes (Tyof codes c :++: i) (Tyof codes c :++: j)
  -> ES ki codes (a ': i) (a ': j)
cpy = Cpy

-- In Agda this would be:
-- ++⁻ : {A : Set}
--       {P : A -> Set}
--       (xs : List A)
--       {ys : List A} 
--     → All P (xs ++ ys) → All P xs × All P ys
-- ++⁻ []       p          = [] , p
-- ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (px ∷_) id (++⁻ _ pxs)
--
--   Note in particular, that xs is not an implicit argument,
--   and that we explicitly pattern match on it.
--
--   In haskell, types and values are separated, but we can 
--   carry around the Singleton LstPrf in order to
--   discover on the type-level the list, by pattern matching
split :: ListPrf xs -> NP p (xs :++: ys) -> (NP p xs, NP p ys)
split Nil poa = (NP0, poa)
split (Cons p) (x :* rs) =
  let (xs, rest) = split p rs
   in (x :* xs, rest)

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

-- we need to give Haskell a bit of a hint that Tyof codes c reduces to an IsList
-- insCof is also really the only place where we _need_ IsList I think
insCof 
  :: ListPrf xs 
  -> ListPrf (Tyof codes c)
  -> Cof ki codes a c
  -> PoA ki (Fix ki codes) (Tyof codes c :++: xs)
  -> PoA ki (Fix ki codes) (a ': xs)
insCof isxs ispoa c xs =
  let (args, rest) = split ispoa xs
   in injCof c args :* rest

delCof ::
     Eq1 ki
  => Cof ki codes a c
  -> PoA ki (Fix ki codes) (a ': xs)
  -> Maybe (PoA ki (Fix ki codes) (Tyof codes c :++: xs))
delCof c (x :* xs) = flip appendNP xs <$> matchCof c x



diff :: forall fam ki codes ix1 ix2 ty1 ty2.
     ( Family ki fam codes
     , ix1 ~ Idx ty1 fam
     , ix2 ~ Idx ty2 fam
     , Lkup ix1 fam ~ ty1
     , Lkup ix2 fam ~ ty2
     , IsNat ix1
     , IsNat ix2
     , Digestible1 ki, Eq1 ki
     , TestEquality ki
     )
  => ty1
  -> ty2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff a b = diff' (deep a) (deep b)

diff' ::
     (Digestible1 ki, Eq1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff' a b = getDiff $ diff'' a b

apply ::
     forall ki fam codes ty1 ty2 ix1 ix2.
     ( Family ki fam codes
     , ix1 ~ Idx ty1 fam
     , ix2 ~ Idx ty2 fam
     , Lkup ix1 fam ~ ty1
     , Lkup ix2 fam ~ ty2
     , IsNat ix1
     , IsNat ix2
     , Digestible1 ki, Eq1 ki
     , TestEquality ki
     )
  => ES ki codes '[ 'I ix1] '[ 'I ix2]
  -> ty1
  -> Maybe ty2
apply es a =
  case apply' es (deep a) of
    Just (Fix x) ->
      case dto @ix2 x of
        El b -> Just b
    Nothing -> Nothing

apply' ::
     (IsNat ix1, IsNat ix2, Digestible1 ki, Eq1 ki)
  => ES ki codes '[ 'I ix1] '[ 'I ix2]
  -> Fix ki codes ix1
  -> Maybe (Fix ki codes ix2)
apply' es x = do
  x <- applyES es (NA_I x :* NP0)
  case x of
    (NA_I y :* NP0) -> pure y

applyES ::
     Eq1 ki
  => ES ki codes xs ys
  -> PoA ki (Fix ki codes) xs
  -> Maybe (PoA ki (Fix ki codes) ys)
applyES ES0 x = Just NP0
applyES (Ins isys ispoa _ c es) xs = insCof isys ispoa c <$> applyES es xs
applyES (Del isxs ispoa _ c es) xs = delCof c xs >>= applyES es
applyES (Cpy isxs isys ispoa _ c es) xs = insCof isys ispoa c <$> (delCof c xs >>= applyES es)

-- {-# INLINE cost #-}
--
--  IDEA: Instead of calculating cost every time (Expensive)
--  build up cost by construction (We get it for free)
cost :: ES ki codes txs tys -> Int
cost ES0 = 0
cost (Ins _ _ k c es) = k
cost (Del _ _ k c es) = k
cost (Cpy _ _ _ k c es) = k

-- {-# INLINE meet #-}
meet :: ES ki codes txs tys -> ES ki codes txs tys -> ES ki codes txs tys
meet d1 d2 =
  if cost d1 <= cost d2
    then d1
    else d2

-- ********* MEMOIZATION **************
data EST (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES ki codes '[] '[] -> EST ki codes '[] '[]
  NC
    :: ListPrf tys
    -> ListPrf (Tyof codes c)
    -> Cof ki codes y c
    -> ES ki codes '[] (y ': tys)
    -> EST ki codes '[] (Tyof codes c :++: tys)
    -> EST ki codes '[] (y ': tys)
  CN
   :: ListPrf txs
   -> ListPrf (Tyof codes c)
   -> Cof ki codes x c
   -> ES ki codes (x ': txs) '[]
   -> EST ki codes (Tyof codes c :++: txs) '[]
   -> EST ki codes (x ': txs) '[]
  CC
    :: ListPrf txs
    -> ListPrf (Tyof codes cx)
    -> ListPrf tys
    -> ListPrf (Tyof codes cy)
    -> Cof ki codes x cx
    -> Cof ki codes y cy
    -> ES ki codes (x ': txs) (y ': tys)
    -> EST ki codes (x ': txs) (Tyof codes cy :++: tys)
    -> EST ki codes (Tyof codes cx :++: txs) (y ': tys)
    -> EST ki codes (Tyof codes cx :++: txs) (Tyof codes cy :++: tys)
    -> EST ki codes (x ': txs) (y ': tys)

nc ::
     ListPrf tys
  -> ListPrf (Tyof codes c)
  -> Cof ki codes y c
  -> ES ki codes '[] (y ': tys)
  -> EST ki codes '[] (Tyof codes c :++: tys)
  -> EST ki codes '[] (y ': tys)
nc = NC

cn
  :: ListPrf txs
  -> ListPrf (Tyof codes c)
  -> Cof ki codes x c
  -> ES ki codes (x ': txs) '[]
  -> EST ki codes (Tyof codes c :++: txs) '[]
  -> EST ki codes (x ': txs) '[]
cn = CN

cc 
  :: ListPrf txs
  -> ListPrf (Tyof codes cx)
  -> ListPrf tys
  -> ListPrf (Tyof codes cy)
  -> Cof ki codes x cx
  -> Cof ki codes y cy
  -> ES ki codes (x ': txs) (y ': tys)
  -> EST ki codes (x ': txs) (Tyof codes cy :++: tys)
  -> EST ki codes (Tyof codes cx :++: txs) (y ': tys)
  -> EST ki codes (Tyof codes cx :++: txs) (Tyof codes cy :++: tys)
  -> EST ki codes (x ': txs) (y ': tys)
cc = CC

getDiff :: forall ki codes rxs rys. EST ki codes rxs rys -> ES ki codes rxs rys
getDiff (NN x) = x
getDiff (NC _ _ _ x _) = x
getDiff (CN _ _ _ x _) = x
getDiff (CC _ _ _ _ _ _ x _ _ _) = x

-- in order to match a constructor of an Atom
-- we will try all possible constructors, and once we find one that
-- matches, we tell you which constructor it was,
-- and a proof that that it's indeed of the correct type
--
--
--   The gdiff lib wants a   ListPrf (tyof codes c)
--   but we have a NP p (Tyof codes c)
--
--   however, we can't make a function   NP p xs -> ListPrf xs
--   as the constructors of NP don't carry the List proof
matchConstructor ::
     NA ki (AnnFix ki codes phi) a
  -> (forall c. Cof ki codes a c -> ListPrf (Tyof codes c) -> PoA ki (AnnFix ki codes phi) (Tyof codes c) -> r)
  -> r
matchConstructor (NA_K k) f = f (ConstrK k) Nil NP0
matchConstructor (NA_I (AnnFix _ rep)) f =
  case sop rep of
    Tag c poa -> f (ConstrI c) (listPrfNP poa) poa

-- | Given two deep representations, we get the diff.
-- Here I simply wrap in a List of Atoms, to use diffT, but I'm not sure if I'm right to do so
-- TODO: ask victor
diff'' ::
     (Digestible1 ki, Eq1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> EST ki codes '[ 'I ix1] '[ 'I ix2]
diff'' x y =
  let x' = NA_I (Digest.auth x)
      y' = NA_I (Digest.auth y)
   in diffA x' y'

diffA ::
     (Digestible1 ki, Eq1 ki, TestEquality ki)
  => NA ki (AnnFix ki codes (Const Digest)) x
  -> NA ki (AnnFix ki codes (Const Digest)) y
  -> EST ki codes '[ x] '[ y]
diffA a b = diffPoA (a :* NP0) (b :* NP0)

diffPoA ::
     (Digestible1 ki, Eq1 ki, TestEquality ki)
  => PoA ki (AnnFix ki codes (Const Digest)) '[ x]
  -> PoA ki (AnnFix ki codes (Const Digest)) '[ y]
  -> EST ki codes '[ x] '[ y]
diffPoA = diffT

diffT ::
     forall xs ys ki codes. (Digestible1 ki, Eq1 ki, TestEquality ki, L2 xs ys)
  => PoA ki (AnnFix ki codes (Const Digest) ) xs
  -> PoA ki (AnnFix ki codes (Const Digest) ) ys
  -> EST ki codes xs ys
diffT = diffT' (listPrf :: ListPrf xs) (listPrf :: ListPrf ys)

cpyTreeT
  :: (Eq1 ki, TestEquality ki)
  => NA ki (AnnFix ki codes (Const Digest)) a
  -> EST ki codes '[ a ] '[ a ]
cpyTreeT x = cpyTreeT' (Cons Nil) (x :* NP0)

cpyTreeT'
  :: (Eq1 ki, TestEquality ki)
  => ListPrf xs
  -> PoA ki (AnnFix ki codes (Const Digest)) xs
  -> EST ki codes xs xs
cpyTreeT' Nil NP0 = NN ES0
cpyTreeT' (Cons isxs) (x :* xs) = 
  matchConstructor x $ \c ispoa poa ->
    let
      c' = cpyTreeT' (appendIsListLemma ispoa isxs) (appendNP poa xs)
    in
      cc 
        isxs ispoa isxs ispoa c c (cpy isxs isxs ispoa 0 c (getDiff c')) 
        -- TODO faster version of extendi that only considers cpy 
        -- and thus does not call bestDiffT
        (extendi ispoa isxs c c')
        (extendd ispoa isxs c c')
        c'

diffT' ::
     (Digestible1 ki, Eq1 ki, TestEquality ki)
  => ListPrf xs
  -> ListPrf ys
  -> PoA ki (AnnFix ki codes (Const Digest)) xs
  -> PoA ki (AnnFix ki codes (Const Digest)) ys
  -> EST ki codes xs ys
diffT' Nil Nil NP0 NP0 = NN ES0
diffT' (Cons isxs) Nil (x :* xs) NP0 =
  matchConstructor x $ \cx isxs' xs' ->
    let d = diffT' (appendIsListLemma isxs' isxs) Nil (appendNP xs' xs) NP0
        d' = getDiff d
     in cn isxs isxs' cx (del isxs isxs' (1 + cost d') cx d') d
      -- TODO(1) use smart constructors! CN c (Del c (getDiff d)) d
diffT' Nil (Cons isys) NP0 (y :* ys) =
  matchConstructor y $ \c isys' ys' ->
    let i = diffT' Nil (appendIsListLemma isys' isys) NP0 (appendNP ys' ys)
        i' = getDiff i 
     in nc isys isys' c (ins isys isys' (1 + cost i') c i') i
diffT' (Cons isxs) (Cons isys) (x :* xs) (y :* ys) =
  case (hashEq x y, xs, ys) of
    -- if two subtrees are equal, we just copy it directly
    (Just Refl, NP0, NP0) ->
      cpyTreeT x
    _ -> 
      matchConstructor x $ \cx isxs' xs' ->
        matchConstructor y $ \cy isys' ys' ->
          let i = extendi isxs' isxs cx c
              d = extendd isys' isys cy c
              -- NOTE, c is shared to calculate i and d!
              c =
                diffT'
                  (appendIsListLemma isxs' isxs)
                  (appendIsListLemma isys' isys)
                  (appendNP xs' xs)
                  (appendNP ys' ys)
           in cc
                isxs
                isxs'
                isys
                isys'
                cx
                cy
                (bestDiffT cx cy isxs isxs' isys isys' i d c)
                i
                d
                c

extendd ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cy)
  -> ListPrf ys
  -> Cof ki codes y cy
  -> EST ki codes xs (Tyof codes cy :++: ys)
  -> EST ki codes xs (y ': ys)
extendd isys' isys cy dt@(NN d) = nc isys isys' cy (ins isys isys' (1 + cost d) cy d) dt
extendd isys' isys cy dt@(NC _ _  _ d _) = nc isys isys' cy (ins isys isys' (1 + cost d) cy d) dt
extendd isys' isys cy dt@(CN _ _ _ _ _) = extendd' isys' isys cy dt
extendd isys' isys cy dt@(CC _ _ _ _ _ _ _ _ _ _) = extendd' isys' isys cy dt

extendd' ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cy)
  -> ListPrf ys
  -> Cof ki codes y cy
  -> EST ki codes (x ': xs) (Tyof codes cy :++: ys)
  -> EST ki codes (x ': xs) (y ': ys)
extendd' isys' isys cy dt =
  extractd dt $ \isxs' isxs cx dt' ->
    let i = dt
        d = extendd isys' isys cy dt'
        c = dt'
     in cc
          isxs
          isxs'
          isys
          isys'
          cx
          cy
          (bestDiffT cx cy isxs isxs' isys isys' i d c)
          i
          d
          c

extractd ::
     TestEquality ki
  => EST ki codes (x ': xs) ys'
  -> (forall cx. ListPrf (Tyof codes cx) -> ListPrf xs -> Cof ki codes x cx -> EST ki codes (Tyof codes cx :++: xs) ys' -> r)
  -> r
extractd (CC _ isxs _ isys c _ d' _ d _) k = k isxs (sourceTail d') c d
extractd (CN _ isxs c d' d) k = k isxs (sourceTail d') c d

extendi ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cx)
  -> ListPrf xs
  -> Cof ki codes x cx
  -> EST ki codes (Tyof codes cx :++: xs) ys
  -> EST ki codes (x ': xs) ys
extendi isxs' isxs cx dt@(NN d) = cn isxs isxs' cx (del isxs isxs' (1 + cost d) cx d) dt
extendi isxs' isxs cx dt@(CN _ _ _ d _) = cn isxs isxs' cx (del isxs isxs' (1 + cost d) cx d) dt
extendi isxs' isxs cx dt@(NC _ _ _ _ _) = extendi' isxs' isxs cx dt
extendi isxs' isxs cx dt@(CC _ _ _ _ _ _ _ _ _ _) = extendi' isxs' isxs cx dt

extendi' ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cx)
  -> ListPrf xs
  -> Cof ki codes x cx
  -> EST ki codes (Tyof codes cx :++: xs) (y ': ys)
  -> EST ki codes (x : xs) (y ': ys)
extendi' isxs' isxs cx dt =
  extracti dt $ \isys' isys cy dt' ->
    let i = extendi isxs' isxs cx dt'
        d = dt
        c = dt'
     in cc
          isxs
          isxs'
          isys
          isys'
          cx
          cy
          (bestDiffT cx cy isxs isxs' isys isys' i d c)
          i
          d
          c

cofToListPrf ::
     IsList (Tyof codes cy) => Cof ki codes y cy -> ListPrf (Tyof codes cy)
cofToListPrf _ = listPrf

-- Most time is now spent around marshalling list proofs
-- Question: Do we actually need these list proofs?
sourceTail :: ES ki codes (x ': xs) ys -> ListPrf xs
sourceTail (Ins x y _ _ d) = sourceTail d
sourceTail (Del x y _ _ _) = x
sourceTail (Cpy x y z _ _ _) = x

targetTail :: ES ki codes xs (y ': ys) -> ListPrf ys
targetTail (Ins x y _ _ d) = x
targetTail (Del x y _ _ d) = targetTail d
targetTail (Cpy x y z _ _ _) = y

extracti ::
     (Eq1 ki, TestEquality ki)
  => EST ki codes xs' (y ': ys)
  -> (forall cy. ListPrf (Tyof codes cy)
              -> ListPrf ys
              -> Cof ki codes y cy 
              -> EST ki codes xs' (Tyof codes cy :++: ys) 
              -> r)
  -> r
extracti (CC _ isxs _ isys _ c d i _ _) k = k isys (targetTail d) c i
extracti (NC _ isxs c d i) k = k isxs (targetTail d) c i

bestDiffT ::
     (Eq1 ki, TestEquality ki)
  => Cof ki codes x cx
  -> Cof ki codes y cy
  -> ListPrf xs
  -> ListPrf (Tyof codes cx)
  -> ListPrf ys
  -> ListPrf (Tyof codes cy)
  -> EST ki codes (x ': xs) (Tyof codes cy :++: ys)
  -> EST ki codes (Tyof codes cx :++: xs) (y ': ys)
  -> EST ki codes (Tyof codes cx :++: xs) (Tyof codes cy :++: ys)
  -> ES ki codes (x ': xs) (y ': ys)
bestDiffT cx cy isxs isxs' isys isys' i d c =
  case heqCof cx cy of
    Just (Refl, Refl) ->
      -- TODO: I think this is a bug, we need to consider inserts
      -- or deletes as well? 
      let c' = getDiff c
      in cpy isxs isys isxs' (cost c') cx c' -- cpy isxs' isxs isys cx (getDiff c)
    Nothing ->
      -- TOD: It's wasteful to calculate cost every time. Lets do this instead
      -- costI = getCost (getDiff i)
      -- costD = getCost (getDiff d)
      --
      -- if costI <= costD
      --  then  ins (1 + costI)  (getDiff i)
      --  else  del (1 + costD)  (getDiff d)
      --
      -- this will stop us from calculating cost Over and Over again
      let i' = getDiff i
          d' = getDiff d
      in meet (ins isys isys' (1 + cost i') cy i') (del isxs isxs' (1 + cost d') cx d')
