{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.GDiff where
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
  Cons :: IsList l => ListPrf l ->  ListPrf (x ': l)


type L1 xs = (IsList xs) 
type L2 xs ys = (IsList xs, IsList ys) 
type L3 xs ys zs = (IsList xs, IsList ys, IsList zs) 
type L4 xs ys zs as = (IsList xs, IsList ys, IsList zs, IsList as) 

instance IsList '[] where
  isList = Nil

instance IsList xs => IsList (x ': xs) where
  isList = Cons isList

  
data Cof (ki :: kon -> *) (codes :: [[[Atom kon]]]) 
         (a :: Atom kon) (c :: SinglCof) where
  ConstrI :: IsNat n => Constr c (Lkup n codes)  -> Cof ki codes (I n) (CofI n c)
  ConstrK :: ki k                  -> Cof ki codes (K k) CofK

type family Tyof (codes :: [[[Atom kon]]]) (c :: SinglCof) 
    :: [Atom kon] where
  -- we wanted Lkup c . Lkup ix but haskell complains
  -- jTyof (f ': codes) (CofI Z      c) = Lkup c f
  -- Tyof (f ': codes) (CofI (S ix) c) = Tyof codes (CofI ix c)
  Tyof codes (CofI ix c) = Lkup c (Lkup ix codes)
  Tyof codes CofK        = '[]

data ES (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  ES0 :: ES ki codes '[] '[]
  Ins :: L3 i j (Tyof codes c) => Cof ki codes a c 
      -> ES ki codes i (Append (Tyof codes c) j)
      -> ES ki codes i (a ': j)
  Del :: L3 i j (Tyof codes c) => Cof ki codes a c
      -> ES ki codes (Append (Tyof codes c) i) j
      -> ES ki codes (a ': i) j
  Cpy :: L3 i j (Tyof codes c) => Cof ki codes a c 
      -> ES ki codes (Append (Tyof codes c) i) (Append (Tyof codes c) j)
      -> ES ki codes (a ': i) (a ': j)


npCat :: forall p xs ys. (L2 xs ys) 
      => NP p xs -> NP p ys -> NP p (Append xs ys)
npCat poa poa'
  = case isList :: ListPrf xs of
      Nil -> case poa of
               NP0 -> poa'
      Cons pfr -> case poa of
                    (x :* xs) -> x :* npCat xs poa'
   
split :: forall xs ys p . (L2 xs ys) => NP p (Append xs ys) -> (NP p xs, NP p ys)
split poa =
  case isList :: ListPrf xs of
    Nil    -> (NP0, poa)
    Cons _ ->
      case poa of
        (x :* rs) -> 
          let (xs , rest) = split rs
          in (x :* xs , rest)


injCof :: Cof ki codes a c 
       -> PoA ki (Fix ki codes) (Tyof codes c) 
       -> NA ki (Fix ki codes) a
injCof (ConstrI c) xs = NA_I (Fix $ inj c xs)
injCof (ConstrK k) xs = NA_K k

-- TODO(arianvp): This typeclass probably exsists in hackage somwhere already. Also, it should _not_ live here :)
class Eq1 (f :: k -> *) where
  equal :: forall k . f k -> f k -> Bool


matchCof :: (Eq1 ki) 
  => Cof ki codes a c
  -> NA ki (Fix ki codes) a
  -> Maybe (PoA ki (Fix ki codes) (Tyof codes c))
matchCof (ConstrI c1) (NA_I (Fix x)) = match c1 x
matchCof (ConstrK k) (NA_K k2) = 
  guard (equal k k2) >> Just NP0


-- we need to give Haskell a bit of a hint that Tyof codes c reduces to an IsList
insCof :: forall ki codes a c xs. (IsList xs, IsList (Tyof codes c))
       => Cof ki codes a c 
       -> PoA ki (Fix ki codes) (Append (Tyof codes c) xs) 
       -> PoA ki (Fix ki codes) (a ': xs)
insCof c xs 
  = let (args , rest) = split @(Tyof codes c) @xs xs
     in injCof c args :* rest


delCof :: forall ki codes a c xs ys. (Eq1 ki, IsList xs, IsList (Tyof codes c))
       => Cof ki codes a c
       -> PoA ki (Fix ki codes) (a ': xs)
       -> Maybe (PoA ki (Fix ki codes) (Append (Tyof codes c) xs))
delCof c (x :* xs) = case matchCof c x of
  Just poa -> Just (npCat poa xs)
  Nothing -> Nothing


applyES :: Eq1 ki => ES ki codes xs ys -> PoA ki (Fix ki codes) xs -> Maybe (PoA ki (Fix ki codes) ys)
applyES ES0 x = Just NP0
applyES (Ins c es) xs = insCof c <$> applyES es xs
  where
applyES (Del c es) xs = delCof c xs >>= applyES es
applyES (Cpy c es) xs = insCof c <$> (delCof c xs >>= applyES es)


cost :: ES ki codes txs tys -> Int
cost ES0 = 0
cost (Ins c es) = 1 + cost es
cost (Del c es) = 1 + cost es
cost (Cpy c es) = cost es

meet :: ES ki codes txs tys -> ES ki codes txs tys -> ES ki codes txs tys
meet d1 d2 = if cost d1 <= cost d2 then d1 else d2


data EST (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES  ki codes '[] '[] 
     -> EST ki codes '[] '[]
  NC :: L2 tys (Tyof codes c) => Cof ki codes y c
     -> ES  ki codes '[] (y ': tys)
     -> EST ki codes '[] (Append (Tyof codes c) tys)
     -> EST ki codes '[] (y ': tys)
  CN :: L2 txs (Tyof codes c) => Cof ki codes x c 
     -> ES  ki codes (x ': txs) '[]
     -> EST ki codes (Append (Tyof codes c) txs) '[]
     -> EST ki codes (x ': txs) '[]
  CC :: L4 txs tys (Tyof codes cy) (Tyof codes cx) => Cof ki codes x cx
     -> Cof ki codes y cy
     -> ES ki codes (x ': txs) (y ': tys)
     -> EST ki codes (x ': txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (y ': tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (x ': txs) (y ': tys)

getDiff :: forall ki codes rxs rys. EST ki codes rxs rys -> ES ki codes rxs rys
getDiff (NN x)  = x
getDiff (NC _ x _) = x
getDiff (CN _ x _) = x
getDiff (CC _ _ x _ _ _) = x


best 
  :: Cof ki codes tx cx 
  -> Cof ki codes ty cy
  -> EST ki codes (tx ': txs)                  (Append (Tyof codes cy) tys)
  -> EST ki codes (Append (Tyof codes cx) txs) (ty ': tys)
  -> EST ki codes (Append (Tyof codes cx) txs) (Append (Tyof codes cy) tys)
  -> ES  ki codes (tx ': txs)                   (ty ': tys)
best = undefined
    

extracti
  :: L3 txs tys (Tyof codes cy)
  => EST ki codes txs (ty ': tys)
  -> ((Cof ki codes ty cy) -> EST ki codes txs (Append (Tyof codes cy) tys) -> r)
  -> r
extracti (CC _ c d i _ _) k = _
extracti (NC c d i) k = _

extractd
  :: EST ki codes (tx ': txs) tys
  -> ((Cof ki codes tx cx) -> EST ki codes (Append (Tyof codes cx) txs) tys-> r)
  -> r
extractd = undefined


extendi
  :: L3 txs tys (Tyof codes cx)
  => Cof ki codes tx cx
  -> EST ki codes (Append (Tyof codes cx) txs) tys
  -> EST ki codes (tx ': txs) tys
extendi cx dt@(NN d) = CN cx (Del cx d) dt
extendi cx dt@(CN _ d _) =  CN cx (Del cx d) dt
extendi cx dt@(NC _ _ _) = extendi' cx dt
extendi cx dt@(CC _ _ _ _ _ _) = extendi' cx dt

extendi'
  :: L3 txs tys (Tyof codes cx)
  => Cof ki codes tx cx 
  -> EST ki codes (Append (Tyof codes cx) txs) (ty ': tys)
  -> EST ki codes (tx ': txs) (ty ': tys)
extendi' cx dt =  undefined


extendd
  :: L3 txs tys (Tyof codes cy)
  => Cof ki codes ty cy
  -> EST ki codes txs (Append (Tyof codes cy) tys) 
  -> EST ki codes txs (ty ': tys)
extendd = undefined

diffT
  :: forall xs ys ki codes. L2 xs ys 
  => PoA ki (Fix ki codes) xs
  -> PoA ki (Fix ki codes) ys
  -> EST ki codes xs ys
diffT = diffT' (isList :: ListPrf xs) (isList :: ListPrf ys)


-- Okay lets do diffT on listPrfs instead, which is a bit easier

diffT'
  :: ListPrf xs 
  -> ListPrf ys
  -> PoA ki (Fix ki codes) xs
  -> PoA ki (Fix ki codes) ys
  -> EST ki codes xs ys
diffT' = undefined

{-diffT :: PoA ki (Fix ki codes) txs -> PoA ki (Fix ki codes) tys -> EST txs tys 
diffT = _

-}
