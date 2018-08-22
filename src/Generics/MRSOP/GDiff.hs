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
import Generics.MRSOP.Base
import Generics.MRSOP.Base.Metadata
import Generics.MRSOP.GDiff.Util
import Generics.MRSOP.Util
import Data.Digems.Generic.Digest (Digest, Digestible1)
import qualified Data.Digems.Generic.Digest as Digest
import qualified Generics.MRSOP.AG as AG

data Ann = Copy | Modify

copyOrModify :: Eq a => Const a ix -> Const a ix -> Const Ann ix
copyOrModify (Const x) (Const y) = if x == y then Const Copy else Const Modify

-- | Given a tree that's annotated with some decision about its content
-- decide what parts to copy or modify
findCopies
  :: Eq a
  => AnnFix ki codes (Const a) ix
  -> AnnFix ki codes (Const a) ix
  -> AnnFix ki codes (Const Ann) ix
findCopies = AG.zipAnn copyOrModify




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
    Just Refl | eq1 x y -> Just (Refl, Refl)
    _ -> Nothing
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
    :: L2 j (Tyof codes c)
    => Int
    -> Cof ki codes a c
    -> ES ki codes i (Tyof codes c :++: j)
    -> ES ki codes i (a ': j)
  Del
    :: L2 i (Tyof codes c)
    => Int
    -> Cof ki codes a c
    -> ES ki codes (Tyof codes c :++: i) j
    -> ES ki codes (a ': i) j
  Cpy
    :: L3 i j (Tyof codes c)
    => Int
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
  show (Ins _ c d) = "Ins " ++ showCof c ++ " $ " ++ show d
  show (Del _ c d) = "Del " ++ showCof c ++ " $ " ++ show d
  show (Cpy _ c d) = "Cpy " ++ showCof c ++ " $ " ++ show d

-- Smart constructors 
-- TODO this is incorrect. I should only pass  ListPrf (Tyof codes c) and ListPrf j
ins ::
     ListPrf j
  -> ListPrf (Tyof codes c)
  -> Int
  -> Cof ki codes a c
  -> ES ki codes i (Tyof codes c :++: j)
  -> ES ki codes i (a ': j)
ins pj pty =
  case (reify pj, reify pty) of
    (RList, RList) -> Ins

del ::
     ListPrf i
  -> ListPrf (Tyof codes c)
  -> Int
  -> Cof ki codes a c
  -> ES ki codes (Tyof codes c :++: i) j
  -> ES ki codes (a ': i) j
del pi pty =
  case (reify pi, reify pty) of
    (RList, RList) -> Del


cpy ::
     ListPrf i
  -> ListPrf j
  -> ListPrf (Tyof codes c)
  -> Int
  -> Cof ki codes a c
  -> ES ki codes (Tyof codes c :++: i) (Tyof codes c :++: j)
  -> ES ki codes (a ': i) (a ': j)
cpy pi pj pty =
  case (reify pi, reify pj, reify pty) of
    (RList, RList, RList) -> Cpy 

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
insCof ::
     forall ki codes a c xs. (IsList xs, IsList (Tyof codes c))
  => Cof ki codes a c
  -> PoA ki (Fix ki codes) (Tyof codes c :++: xs)
  -> PoA ki (Fix ki codes) (a ': xs)
insCof c xs =
  let (args, rest) = split (listPrf :: ListPrf (Tyof codes c)) xs
   in injCof c args :* rest

delCof ::
     Eq1 ki
  => Cof ki codes a c
  -> PoA ki (Fix ki codes) (a ': xs)
  -> Maybe (PoA ki (Fix ki codes) (Tyof codes c :++: xs))
delCof c (x :* xs) = flip appendNP xs <$> matchCof c x

apply ::
     forall ki fam codes ty1 ty2 ix1 ix2.
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
  => ES ki codes '[ 'I ix1] '[ 'I ix2]
  -> ty1
  -> Maybe ty2
apply es a =
  case apply' es (deep a) of
    Just (Fix x) ->
      case dto @ix2 x of
        El b -> Just b
    Nothing -> Nothing

diff :: forall fam ki codes ix1 ix2 ty1 ty2.
     ( Family ki fam codes
     , ix1 ~ Idx ty1 fam
     , ix2 ~ Idx ty2 fam
     , Lkup ix1 fam ~ ty1
     , Lkup ix2 fam ~ ty2
     , IsNat ix1
     , IsNat ix2
     , Eq1 ki
     , Digestible1 ki
     , TestEquality ki
     )
  => ty1
  -> ty2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff a b = diff' (deep a) (deep b)

diff' ::
     (Eq1 ki, Digestible1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff' a b = getDiff $ diff'' a b

apply' ::
     (IsNat ix1, IsNat ix2, Eq1 ki)
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
applyES (Ins _ c es) xs = insCof c <$> applyES es xs
applyES (Del _ c es) xs = delCof c xs >>= applyES es
applyES (Cpy _ c es) xs = insCof c <$> (delCof c xs >>= applyES es)

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

-- ********* MEMOIZATION **************
data EST (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES ki codes '[] '[] -> EST ki codes '[] '[]
  NC
    :: L2 tys (Tyof codes c)
    => Cof ki codes y c
    -> ES ki codes '[] (y ': tys)
    -> EST ki codes '[] (Tyof codes c :++: tys)
    -> EST ki codes '[] (y ': tys)
  CN
    :: L2 txs (Tyof codes c)
    => Cof ki codes x c
    -> ES ki codes (x ': txs) '[]
    -> EST ki codes (Tyof codes c :++: txs) '[]
    -> EST ki codes (x ': txs) '[]
  CC
    :: L4 txs tys (Tyof codes cy) (Tyof codes cx)
    => Cof ki codes x cx
    -> Cof ki codes y cy
    -> ES ki codes (x ': txs) (y ': tys)                              -- best so far
    -> EST ki codes (x ': txs) (Tyof codes cy :++: tys)               -- insert
    -> EST ki codes (Tyof codes cx :++: txs) (y ': tys)               -- delete
    -> EST ki codes (Tyof codes cx :++: txs) (Tyof codes cy :++: tys) -- copy
    -> EST ki codes (x ': txs) (y ': tys)

nc ::
     ListPrf tys
  -> ListPrf (Tyof codes c)
  -> Cof ki codes y c
  -> ES ki codes '[] (y ': tys)
  -> EST ki codes '[] (Tyof codes c :++: tys)
  -> EST ki codes '[] (y ': tys)
nc a b =
  case (reify a, reify b) of
    (RList, RList) -> NC

cn ::
     ListPrf txs
  -> ListPrf (Tyof codes c)
  -> Cof ki codes x c
  -> ES ki codes (x ': txs) '[]
  -> EST ki codes (Tyof codes c :++: txs) '[]
  -> EST ki codes (x ': txs) '[]
cn a b =
  case (reify a, reify b) of
    (RList, RList) -> CN

cc ::
     ListPrf txs
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
cc a b c d =
  case (reify a, reify b, reify c, reify d) of
    (RList, RList, RList, RList) -> CC

getDiff :: forall ki codes rxs rys. EST ki codes rxs rys -> ES ki codes rxs rys
getDiff (NN x) = x
getDiff (NC _ x _) = x
getDiff (CN _ x _) = x
getDiff (CC _ _ x _ _ _) = x

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

diff'' ::
     (Eq1 ki, Digestible1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> EST ki codes '[ 'I ix1] '[ 'I ix2]
diff'' x y =
  let x' = NA_I (Digest.auth x)
      y' = NA_I (Digest.auth y)
   in diffA x' y'

diffA ::
     (Eq1 ki, TestEquality ki)
  => NA ki (AnnFix ki codes (Const Digest)) x
  -> NA ki (AnnFix ki codes (Const Digest)) y
  -> EST ki codes '[ x] '[ y]
diffA a b = diffPoA (a :* NP0) (b :* NP0)

diffPoA ::
     (Eq1 ki, TestEquality ki, IsList xs, IsList ys)
  => PoA ki (AnnFix ki codes (Const Digest)) xs
  -> PoA ki (AnnFix ki codes (Const Digest)) ys
  -> EST ki codes xs ys
diffPoA = diffT

diffT ::
     forall xs ys ki codes. (Eq1 ki, TestEquality ki, L2 xs ys)
  => PoA ki (AnnFix ki codes (Const Digest)) xs
  -> PoA ki (AnnFix ki codes (Const Digest)) ys
  -> EST ki codes xs ys
diffT xs ys = diffT' (listPrf :: ListPrf xs) (listPrf :: ListPrf ys) xs ys


-- produces the trivial edit script that maps a tree to itself
cpyTree'
  :: (Eq1 ki) 
   => ListPrf xs
  -> PoA ki (AnnFix ki codes (Const Digest)) xs
  -> ES ki codes xs xs
cpyTree' Nil NP0 = ES0
cpyTree' (Cons isxs) (x :* xs) =
  matchConstructor x $ \c ispoa poa -> 
    cpy isxs isxs ispoa 0 c (cpyTree' (appendIsListLemma ispoa isxs) (appendNP poa xs))

cpyTree
  :: (Eq1 ki, IsNat ix)
  => AnnFix ki codes (Const Digest) ix
  -> ES ki codes '[ 'I ix ] '[ 'I ix ]
cpyTree x = cpyTree' (Cons Nil) (NA_I x :* NP0)
  
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
        (extendi ispoa isxs c c')
        (extendd ispoa isxs c c')
        c'


-- | Tests if two trees are equal, based on their annotated hash
hashEq
  :: (TestEquality ki, Eq1 ki) 
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

diffT' ::
     (Eq1 ki, TestEquality ki)
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
              c =
                diffT'
                  (appendIsListLemma isxs' isxs)
                  (appendIsListLemma isys' isys)
                  (appendNP xs' xs)
                  (appendNP ys' ys)
           in
                  cc
                    isxs
                    isxs'
                    isys
                    isys'
                    cx
                    cy
                    (bestDiffT cx cy isxs isxs' isys isys' i d c) -- or a copy tree
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
extendd isys' isys cy dt@(NC _ d _) = nc isys isys' cy (ins isys isys' (1 + cost d) cy d) dt
extendd isys' isys cy dt@(CN _ _ _) = extendd' isys' isys cy dt
extendd isys' isys cy dt@(CC _ _ _ _ _ _) = extendd' isys' isys cy dt

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
extractd (CC c _ d' _ d _) k = k (cofToListPrf c) (sourceTail d') c d
extractd (CN c d' d) k = k (cofToListPrf c) (sourceTail d') c d

-- | Takes the shared part dt and adds another a column on top
--
extendi ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cx)
  -> ListPrf xs
  -> Cof ki codes x cx
  -> EST ki codes (Tyof codes cx :++: xs) ys
  -> EST ki codes (x ': xs) ys
extendi isxs' isxs cx dt@(NN d) = cn isxs isxs' cx (del isxs isxs' (1 + cost d) cx d) dt
extendi isxs' isxs cx dt@(CN _ d _) = cn isxs isxs' cx (del isxs isxs' (1 + cost d) cx d) dt
extendi isxs' isxs cx dt@(NC _ _ _) = extendi' isxs' isxs cx dt
extendi isxs' isxs cx dt@(CC _ _ _ _ _ _) = extendi' isxs' isxs cx dt

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
sourceTail (Ins _ _ d) = sourceTail d
sourceTail (Del _ _ _) = listPrf
sourceTail (Cpy _ _ _) = listPrf

targetTail :: ES ki codes xs (y ': ys) -> ListPrf ys
targetTail (Ins _ _ d) = listPrf
targetTail (Del _ _ d) = targetTail d
targetTail (Cpy _ _ _) = listPrf

extracti ::
     (Eq1 ki, TestEquality ki)
  => EST ki codes xs' (y ': ys)
  -> (forall cy. ListPrf (Tyof codes cy) -> ListPrf ys -> Cof ki codes y cy -> EST ki codes xs' (Tyof codes cy :++: ys) -> r)
  -> r
extracti (CC _ c d i _ _) k = k (cofToListPrf c) (targetTail d) c i
extracti (NC c d i) k = k (cofToListPrf c) (targetTail d) c i

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
      let c' = getDiff c
          i' = getDiff i
          d' = getDiff d
      in cpy isxs isys isxs' (cost c') cx c' `meet` 
         ins isys isys' (1 + cost i') cy i' `meet`
         del isxs isxs' (1 + cost d') cx d'
    Nothing ->
      let i' = getDiff i
          d' = getDiff d
      in ins isys isys' (1 + cost i') cy i' `meet` del isxs isxs' (1 + cost d') cx d'


