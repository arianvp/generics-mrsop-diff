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

import Data.Type.Equality
import Control.Monad
import Data.Proxy
import Data.Semigroup
import Generics.MRSOP.Base
import Generics.MRSOP.Util

data SinglCof
  = CofI Nat Nat -- type index and constructor index within the type
  | CofK


type family Append txs tys where
  Append '[] tys = tys
  Append (tx ': txs) tys = tx ': (Append txs tys)


class IsList (xs :: [k]) where
  isList :: ListPrf xs

data ListPrf :: [k] -> * where
  Nil ::  ListPrf '[]
  Cons :: ListPrf l ->  ListPrf (x ': l)

data Trivial :: k -> * where
  MkTrivial :: Trivial k

-- We can have some kind of forgetful functor that ignores p
npToListPrf :: forall xs p. NP p xs -> ListPrf xs
npToListPrf NP0       = Nil
npToListPrf (_ :* xs) = Cons (npToListPrf xs)

-- we can go the other way around. not sure if useful
listPrfToNP :: ListPrf xs -> NP Trivial xs
listPrfToNP Nil = NP0
listPrfToNP (Cons xs) = MkTrivial :* listPrfToNP xs




type L1 xs = (IsList xs) 
type L2 xs ys = (IsList xs, IsList ys) 
type L3 xs ys zs = (IsList xs, IsList ys, IsList zs) 
type L4 xs ys zs as = (IsList xs, IsList ys, IsList zs, IsList as) 

instance IsList '[] where
  isList = Nil

instance IsList xs => IsList (x ': xs) where
  isList = Cons isList


data RList :: [k] -> * where
  RList :: IsList ts => RList ts

reify :: ListPrf ts -> RList ts
reify Nil = RList
reify (Cons x) = case reify x of RList -> RList

  
data Cof (ki :: kon -> *) (codes :: [[[Atom kon]]]) 
         (a :: Atom kon) (c :: SinglCof) where
  ConstrI :: IsNat n => Constr c (Lkup n codes)  -> Cof ki codes (I n) (CofI n c)
  ConstrK :: ki k                  -> Cof ki codes (K k) CofK

cofWitnessI :: Cof ki codes (I n) (CofI n c) -> Proxy n
cofWitnessI _ = Proxy

heqCof :: (TestEquality ki) 
       => Cof ki codes a cx -> Cof ki codes b cy ->  Maybe (a :~: b , cx :~: cy)
heqCof cx@(ConstrI x) cy@(ConstrI y)
  = case testEquality (getSNat (cofWitnessI cx)) (getSNat (cofWitnessI cy)) of
      Nothing   -> Nothing
      Just Refl -> case heqConstr x y of
        Nothing   -> Nothing
        Just Refl -> Just (Refl, Refl)
heqCof (ConstrK x) (ConstrK y)
  = case testEquality x y of
      Just Refl -> Just (Refl , Refl)
      Nothing   -> Nothing
heqCof _ _ = Nothing


type family Tyof (codes :: [[[Atom kon]]]) (c :: SinglCof) 
    :: [Atom kon] where
  -- we wanted Lkup c . Lkup ix but haskell complains
  -- jTyof (f ': codes) (CofI Z      c) = Lkup c f
  -- Tyof (f ': codes) (CofI (S ix) c) = Tyof codes (CofI ix c)
  Tyof codes (CofI ix c) = Lkup c (Lkup ix codes)
  Tyof codes CofK        = '[]

data ES (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  ES0 :: ES ki codes '[] '[]
  Ins :: L2 j (Tyof codes c) => Cof ki codes a c 
      -> ES ki codes i (Append (Tyof codes c) j)
      -> ES ki codes i (a ': j)
  Del :: Cof ki codes a c
      -> ES ki codes (Append (Tyof codes c) i) j
      -> ES ki codes (a ': i) j
  Cpy :: L2 j (Tyof codes c) => Cof ki codes a c 
      -> ES ki codes (Append (Tyof codes c) i) (Append (Tyof codes c) j)
      -> ES ki codes (a ': i) (a ': j)

-- Smart constructors 
-- TODO this is incorrect. I should only pass  ListPrf (Tyof codes c) and ListPrf j
ins
  :: ListPrf j -> ListPrf (Tyof codes c)
  -> Cof ki codes a c 
  -> ES ki codes i (Append (Tyof codes c) j)
  -> ES ki codes i (a ': j)
ins pj pty =
  case (reify pj, reify pty) of
    (RList,RList) -> Ins

del
  :: ListPrf i -> ListPrf (Tyof codes c)
  -> Cof ki codes a c 
  -> ES ki codes (Append (Tyof codes c) i) j
  -> ES ki codes (a ': i) j
del pj pty =
  case (reify pj, reify pty) of
    (RList,RList) -> Del

cpy
  :: ListPrf j -> ListPrf (Tyof codes c)
  -> Cof ki codes a c 
  -> ES ki codes (Append (Tyof codes c) i) (Append (Tyof codes c) j)
  -> ES ki codes (a ': i) (a ': j)
cpy pj pty =
  case (reify pj, reify pty) of
    (RList,RList) -> Cpy


-- why the hell does this not work??
prfCat :: ListPrf xs -> ListPrf ys -> ListPrf (Append xs ys)
prfCat Nil isys = isys
prfCat (Cons isxs) isys = Cons (prfCat isxs isys)

npCat' :: ListPrf xs -> ListPrf ys -> NP p  xs -> NP p ys -> NP p (Append xs ys)
npCat' Nil _ NP0 ays = ays
npCat' (Cons l) r (a :* axs) ays = a :* npCat' l r axs ays

npCat :: NP p xs -> NP p ys -> NP p (Append xs ys)
npCat NP0 ays = ays
npCat (a :* axs) ays = a :* npCat axs ays

-- We need to have some extra proof about the fact that xs and ys
-- are actually lists. Otherwise  split won't work, hence the L2
-- We need to decide whether xs is empty or not
split :: ListPrf xs -> NP p (Append xs ys) -> (NP p xs, NP p ys)
split Nil poa = (NP0, poa)
split (Cons p) (x :* rs) = 
  let
    (xs , rest) = split p rs
  in
    (x :* xs , rest)


injCof
  :: Cof ki codes a c
  -> PoA ki (Fix ki codes) (Tyof codes c)
  -> NA ki (Fix ki codes) a
injCof (ConstrI c) xs = NA_I (Fix $ inj c xs)
injCof (ConstrK k) xs = NA_K k

-- TODO(arianvp): This typeclass probably exsists in hackage somwhere already. Also, it should _not_ live here :)
class Eq1 (f :: k -> *) where
  equal :: forall k . f k -> f k -> Bool


matchCof
  :: (Eq1 ki) 
  => Cof ki codes a c
  -> NA ki (Fix ki codes) a
  -> Maybe (PoA ki (Fix ki codes) (Tyof codes c))
matchCof (ConstrI c1) (NA_I (Fix x)) = match c1 x
matchCof (ConstrK k) (NA_K k2) = 
  guard (equal k k2) >> Just NP0


-- we need to give Haskell a bit of a hint that Tyof codes c reduces to an IsList
-- insCof is also really the only place where we _need_ IsList I think
insCof
  :: forall ki codes a c xs. (IsList xs, IsList (Tyof codes c))
  => Cof ki codes a c 
  -> PoA ki (Fix ki codes) (Append (Tyof codes c) xs) 
  -> PoA ki (Fix ki codes) (a ': xs)
insCof c xs =
  let 
    (args , rest) = split (isList :: ListPrf (Tyof codes c)) xs
  in
    injCof c args :* rest


delCof
  :: Eq1 ki
  => Cof ki codes a c
  -> PoA ki (Fix ki codes) (a ': xs)
  -> Maybe (PoA ki (Fix ki codes) (Append (Tyof codes c) xs))
delCof c (x :* xs) = flip npCat xs <$> matchCof c x

  
applyES
  :: Eq1 ki 
  => ES ki codes xs ys
  -> PoA ki (Fix ki codes) xs
  -> Maybe (PoA ki (Fix ki codes) ys)
applyES ES0 x = Just NP0
applyES (Ins c es) xs = insCof c <$> applyES es xs
applyES (Del c es) xs = delCof c xs >>= applyES es
applyES (Cpy c es) xs = insCof c <$> (delCof c xs >>= applyES es)


cost :: ES ki codes txs tys -> Int
cost ES0 = 0
cost (Ins c es) = 1 + cost es
cost (Del c es) = 1 + cost es
cost (Cpy c es) = cost es

meet :: ES ki codes txs tys -> ES ki codes txs tys -> ES ki codes txs tys
meet d1 d2 = if cost d1 <= cost d2 then d1 else d2



-- ********* MEMOIZATION **************
data EST (ki :: kon -> *)
         (codes :: [[[Atom kon]]]) 
         :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES  ki codes '[] '[] 
     -> EST ki codes '[] '[]
  NC :: L2 tys (Tyof codes c) => Cof ki codes y c
     -> ES  ki codes '[] (y ': tys)
     -> EST ki codes '[] (Append (Tyof codes c) tys)
     -> EST ki codes '[] (y ': tys)
  CN :: Cof ki codes x c 
     -> ES  ki codes (x ': txs) '[]
     -> EST ki codes (Append (Tyof codes c) txs) '[]
     -> EST ki codes (x ': txs) '[]
  CC :: L4 txs tys (Tyof codes cy) (Tyof codes cx)
      => Cof ki codes x cx
     -> Cof ki codes y cy
     -> ES ki codes (x ': txs) (y ': tys)
     -> EST ki codes (x ': txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (y ': tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (x ': txs) (y ': tys)

nc
  :: ListPrf tys 
  -> ListPrf (Tyof codes c) 
  -> Cof ki codes y c
  -> ES  ki codes '[] (y ': tys)
  -> EST ki codes '[] (Append (Tyof codes c) tys)
  -> EST ki codes '[] (y ': tys)
nc a b =
  case (reify a, reify b) of
    (RList, RList) -> NC

cn
  :: ListPrf txs 
  -> ListPrf (Tyof codes c) 
  -> Cof ki codes x c
  -> ES  ki codes (x ': txs) '[]
  -> EST ki codes (Append (Tyof codes c) txs) '[]
  -> EST ki codes (x ': txs) '[]
cn a b =  
  case (reify a, reify b) of
    (RList, RList) -> CN

cc
  :: ListPrf txs
  -> ListPrf (Tyof codes cx)
  -> ListPrf tys
  -> ListPrf (Tyof codes cy)
  -> Cof ki codes x cx
  -> Cof ki codes y cy
  -> ES ki codes (x ': txs) (y ': tys)
  -> EST ki codes (x ': txs) (Append (Tyof codes cy) tys)
  -> EST ki codes (Append (Tyof codes cx) txs) (y ': tys)
  -> EST ki codes (Append (Tyof codes cx) txs) (Append (Tyof codes cy) tys)
  -> EST ki codes (x ': txs) (y ': tys)
cc a b c d =
  case (reify a, reify b, reify c, reify d) of
    (RList, RList, RList, RList) -> CC

getDiff :: forall ki codes rxs rys. EST ki codes rxs rys -> ES ki codes rxs rys
getDiff (NN x)  = x
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
matchConstructor
  :: NA ki (Fix ki codes) a
  ->  (forall c. Cof ki codes a c -> ListPrf (Tyof codes c)
              -> PoA ki (Fix ki codes) (Tyof codes c) -> r)
  -> r
matchConstructor (NA_K k) f =  f (ConstrK  k) Nil NP0
matchConstructor (NA_I (Fix rep)) f =
  case sop rep of
    Tag c poa -> f (ConstrI c) (npToListPrf poa) poa


diffT'
  :: (TestEquality ki)
  => ListPrf xs
  -> ListPrf ys
  -> PoA ki (Fix ki codes) xs
  -> PoA ki (Fix ki codes) ys
  -> EST ki codes xs ys

diffT' Nil Nil NP0 NP0 = NN ES0

diffT' (Cons isxs) Nil (x :* xs) NP0 = 
  matchConstructor x $ \c isxs' xs' -> 
    let
      d = diffT' (prfCat isxs' isxs) Nil (npCat xs' xs) NP0
    in
      CN c (Del c (getDiff d)) d

diffT' Nil (Cons isys) NP0 (y :* ys) =
  matchConstructor y $ \c isys' ys' ->
    let
      i = diffT' Nil (prfCat isys' isys) NP0 (npCat ys' ys)
    in
      nc isys isys' c (ins isys isys' c (getDiff i)) i

diffT' (Cons isxs) (Cons isys) (x :* xs) (y :* ys) =
  matchConstructor x $ \cx isxs' xs' -> matchConstructor y $ \cy isys' ys' ->
    let
      i = extendi isxs' isxs cx c
      d = extendd isys' isys cy c
      c = diffT' (prfCat isxs' isxs) (prfCat isys' isys) (npCat xs' xs) (npCat ys' ys)
    in
      cc isxs isxs' isys isys' cx cy (bestDiffT cx cy isxs isxs' isys isys' i d c) i d c

extendd
  :: TestEquality ki
  => ListPrf (Tyof codes cy)
  -> ListPrf ys
  -> Cof ki codes y cy
  -> EST ki codes xs (Append (Tyof codes cy) ys)
  -> EST ki codes xs (y ': ys)
extendd isys' isys cy dt@(NN d) = nc isys isys' cy (ins isys isys' cy d) dt
extendd isys' isys cy dt@(NC _ d _) = nc isys isys' cy (ins isys isys' cy d) dt
extendd isys' isys cy dt@(CN _ _ _) = extendd' isys' isys cy dt
extendd isys' isys cy dt@(CC _ _ _ _ _ _) = extendd' isys' isys cy dt

extendd'
  :: TestEquality ki
  => ListPrf (Tyof codes cy)
  -> ListPrf ys
  -> Cof ki codes y cy
  -> EST ki codes (x ': xs) (Append (Tyof codes cy) ys) 
  -> EST ki codes (x ': xs) (y ': ys)
extendd' isys' isys cy dt =
  extractd dt $ \ isxs' isxs cx dt' -> undefined


extractd
  :: TestEquality ki
  => EST ki codes (x ': xs) ys'
  -> ( forall cx. ListPrf (Tyof codes cx)
      -> ListPrf xs 
      -> Cof ki codes x cx
      -> EST ki codes (Append (Tyof codes cx) xs)  ys'
      -> r
     )
  -> r
extractd (CC c _ d' _ d _) k =  k (cofToListPrf  c) (sourceTail d') c d
extractd (CN c d' d)       k =  k (cofToListPrf  c) (sourceTail d') c d

extendi
  :: TestEquality ki
  => ListPrf (Tyof codes cx) 
  -> ListPrf xs 
  -> Cof ki codes x cx
  -> EST ki codes (Append (Tyof codes cx) xs) ys
  -> EST ki codes (x ': xs) ys
extendi isxs' isxs cx dt@(NN d) = cn isxs isxs' cx (del isxs isxs' cx d) dt
extendi isxs' isxs cx dt@(CN _ d _) = cn isxs isxs' cx (del isxs isxs' cx d) dt
extendi isxs' isxs cx dt@(NC _ _ _) = extendi' isxs' isxs cx dt
extendi isxs' isxs cx dt@(CC _ _ _ _ _ _) = extendi' isxs' isxs cx dt

extendi'
  :: TestEquality ki
  => ListPrf (Tyof codes cx)
  -> ListPrf xs
  -> Cof ki codes x cx
  -> EST ki codes (Append (Tyof codes cx) xs) (y ': ys)
  -> EST ki codes (x : xs) (y ': ys)
extendi' isxs' isxs cx dt = extracti dt $ \ isys' isys cy dt' ->
  let
    i = extendi isxs' isxs cx dt'
    d = dt
    c = dt'
  in
    cc isxs isxs' isys  isys' cx cy (bestDiffT cx cy isxs isxs' isys isys' i d c) i d c

cofToListPrf :: IsList (Tyof codes cy) => Cof ki codes y cy -> ListPrf (Tyof codes cy)
cofToListPrf _ = isList


sourceTail :: ES ki codes (x ': xs) ys -> ListPrf xs
sourceTail (Ins _ d) = sourceTail d
sourceTail (Del _ _) = isList
sourcetail (Cpy _ _) = isList

targetTail ::  ES ki codes xs (y ': ys) -> ListPrf ys
targetTail (Ins _ d) = isList
targetTail (Del _ d) = targetTail d
targetTail (Cpy _ _) = isList

extracti
  :: TestEquality ki
  => EST ki codes xs' (y ': ys)
  -> ( forall cy. ListPrf (Tyof codes cy)
      -> ListPrf ys 
      -> Cof ki codes y cy
      -> EST ki codes xs' (Append (Tyof codes cy) ys) 
      -> r
     )
  -> r
extracti (CC _ c d i _ _) k = k (_ c) (targetTail d) c i
extracti (NC c d i) k = k (_ c) (targetTail d) c i


best :: ES ki codes xs ys -> ES ki codes xs ys -> ES ki codes xs ys
best dx dy = bestSteps (steps dx) dx (steps dy) dy

steps :: ES ki codes xs ys -> Nat
steps (Ins _ d) = S $ steps d
steps (Del _ d) = S $ steps d
steps (Cpy _ d) = S $ steps d
steps ES0       = Z

bestSteps :: Nat -> d -> Nat -> d -> d
bestSteps Z x _ _ = x
bestSteps _ _ Z y = y
bestSteps (S nx) x (S ny) y = bestSteps nx x ny y

bestDiffT
  :: (TestEquality ki) 
  => Cof ki codes x cx
  -> Cof ki codes y cy
  -> ListPrf xs
  -> ListPrf (Tyof codes cx)
  -> ListPrf ys
  -> ListPrf (Tyof codes cy)
  -> EST ki codes (x ': xs) (Append (Tyof codes cy) ys)
  -> EST ki codes (Append (Tyof codes cx) xs) (y ': ys)
  -> EST ki codes (Append (Tyof codes cx) xs) (Append (Tyof codes cy) ys)
  -> ES ki codes (x ': xs) (y ': ys)
bestDiffT cx cy isxs isxs' isys isys' i d c =
  case heqCof cx cy of
    Just (Refl , Refl) -> cpy isys isxs' cx (getDiff c) -- cpy isxs' isxs isys cx (getDiff c)
    Nothing            ->
      best (ins isys isys' cy (getDiff i)) (del isxs isxs' cx (getDiff d))
      -- _a -- ES ki codes  (x ': xs) (y ': ys)
