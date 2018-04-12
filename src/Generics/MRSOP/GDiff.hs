{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.GDiff where

import Data.Semigroup
import Generics.MRSOP.Base
import Generics.MRSOP.Util
type family Append txs tys where
  Append '[] tys = tys
  Append (tx ': txs) tys = tx ': (Append txs tys)

type family Lool (a :: [Atom kon]) :: * where

data SinglCof
  = CofI Nat Nat -- type index and constructor index within the type
  | CofK

data Cof (ki :: kon -> *) (codes :: [[[Atom kon]]]) 
         (a :: Atom kon) (c :: SinglCof) where
  ConstrI :: Constr c (Lkup n codes)  -> Cof ki codes (I n) (CofI n c)
  ConstrK :: ki k                  -> Cof ki codes (K k) CofK

type family Tyof (codes :: [[[Atom kon]]]) (c :: SinglCof) 
    :: [Atom kon] where
  -- we wanted Lkup c . Lkup ix but haskell complains
  Tyof (f ': codes) (CofI Z      c) = Lkup c f
  Tyof (f ': codes) (CofI (S ix) c) = Tyof codes (CofI ix c)
  Tyof codes CofK        = '[]

data ES (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  Nil :: ES ki codes '[] '[]
  Ins :: Cof ki codes a c 
      -> ES ki codes i (Append (Tyof codes c) j)
      -> ES ki codes i (a ': j)
  Del :: Cof ki codes a c
      -> ES ki codes (Append (Tyof codes c) i) j
      -> ES ki codes (a ': i) j
  Cpy :: Cof ki codes a c 
      -> ES ki codes (Append (Tyof codes c) i) (Append (Tyof codes c) j)
      -> ES ki codes (a ': i) (a ': j)


cost :: ES ki codes txs tys -> Int
cost Nil = 0
cost (Ins c es) = 1 + cost es
cost (Del c es) = 1 + cost es
cost (Cpy c es) = cost es

meet :: ES ki codes txs tys -> ES ki codes txs tys -> ES ki codes txs tys
meet d1 d2 = if cost d1 <= cost d2 then d1 else d2


data EST (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES  ki codes '[] '[] 
     -> EST ki codes '[] '[]
  NC :: Cof ki codes y c
     -> ES  ki codes '[] (y ': ys)
     -> EST ki codes '[] (Append (Tyof codes c) tys)
     -> EST ki codes '[] (y ': tys)
  CN :: Cof ki codes x c 
     -> ES  ki codes (x ': xs) '[]
     -> EST ki codes (Append (Tyof codes c) txs) '[]
     -> EST ki codes (x ': txs) '[]
  CC :: Cof ki codes x cx
     -> Cof ki codes y cy
     -> ES ki codes (x ': txs) (y ': tys)
     -> EST ki codes (x ': txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (y ': tys)
     -> EST ki codes (Append (Tyof codes cx) txs) (Append (Tyof codes cy) tys)
     -> EST ki codes (x ': txs) (y ': tys)
