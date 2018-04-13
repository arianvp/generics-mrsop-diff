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
import Data.Proxy
import Data.Semigroup
import Generics.MRSOP.Base
import Generics.MRSOP.Util
type family Append txs tys where
  Append '[] tys = tys
  Append (tx ': txs) tys = tx ': (Append txs tys)

data SinglCof
  = CofI Nat Nat -- type index and constructor index within the type
  | CofK


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


split :: forall xs ys ki f 
       . (L2 xs ys) => PoA ki f (Append xs ys) 
                    -> (PoA ki f xs, PoA ki f ys)
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
       -> PoA ki (Fix ki codes) (a ': '[])
injCof (ConstrI c) xs = NA_I (Fix $ inj c xs) :* NP0
injCof (ConstrK k) xs = NA_K k :* NP0

-- we need to give Haskell a bit of a hint that Tyof codes c reduces to an IsList
insCof :: forall ki codes a c xs. (IsList xs, IsList (Tyof codes c))
       => Cof ki codes a c 
       -> PoA ki (Fix ki codes) (Append (Tyof codes c) xs) 
       -> PoA ki (Fix ki codes) (a ': xs)
insCof c xs 
  = let (args , rest) = split @(Tyof codes c) @xs xs
     in case injCof c args of
          (x :* NP0) -> (x :* rest)


delCof :: forall ki codes a c xs ys. (IsList xs, IsList (Tyof codes c))
       => Cof ki codes a c
       -> PoA ki (Fix ki codes) (a ': xs)
       -> Maybe (PoA ki (Fix ki codes) (Append (Tyof codes c) xs))
delCof = undefined


applyES :: ES ki codes xs ys -> PoA ki (Fix ki codes) xs -> Maybe (PoA ki (Fix ki codes) ys)
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
     -> ES  ki codes '[] (y ': ys)
     -> EST ki codes '[] (Append (Tyof codes c) tys)
     -> EST ki codes '[] (y ': tys)
  CN :: L2 txs (Tyof codes c) => Cof ki codes x c 
     -> ES  ki codes (x ': xs) '[]
     -> EST ki codes (Append (Tyof codes c) txs) '[]
     -> EST ki codes (x ': txs) '[]
  CC :: L4 txs tys (Tyof codes cy) (Tyof codes cx) => Cof ki codes x cx
     -> Cof ki codes y cy
     -> ES ki codes (x ': txs) (y ': tys)
     -> EST ki codes (x ': txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (y ': tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (x ': txs) (y ': tys)

