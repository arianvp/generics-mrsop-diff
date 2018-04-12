{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.GDiff where

import Generics.MRSOP.Base
import Generics.MRSOP.Util
type family Append txs tys where
  Append '[] tys = tys
  Append (tx ': txs) tys = tx ': (Append txs tys)

type family Lool (a :: [Atom kon]) :: * where

data SinglCof
  = CofI Nat Nat -- type index and constructor index within the type
  | CofK

data Cof (ki :: kon -> *) (fam :: [[[Atom kon]]]) 
         (a :: Atom kon) (c :: SinglCof) where
  ConstrI :: Constr c (Lkup n fam)  -> Cof ki fam (I n) (CofI n c)
  ConstrK :: ki k                  -> Cof ki fam (K k) CofK

type family Tyof (fam :: [[[Atom kon]]]) (c :: SinglCof) 
    :: [Atom kon] where
  -- we wanted Lkup c . Lkup ix but haskell complains
  Tyof (f ': fam) (CofI Z      c) = Lkup c f
  Tyof (f ': fam) (CofI (S ix) c) = Tyof fam (CofI ix c)
  Tyof fam CofK        = '[]

data ES (ki :: kon -> *) (fam :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  Nil :: ES ki fam '[] '[]
  Ins :: Cof ki fam a c 
      -> ES ki fam i (Append (Tyof fam c) j)
      -> ES ki fam i (a ': j)
  Del :: Cof ki fam a c
      -> ES ki fam (Append (Tyof fam c) i) j
      -> ES ki fam (a ': i) j
  Cpy :: Cof ki fam a c 
      -> ES ki fam (Append (Tyof fam c) i) (Append (Tyof fam c) j)
      -> ES ki fam (a ': i) (a ': j)


data EST (ki :: kon -> *) (fam :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES  ki fam '[] '[] 
     -> EST ki fam '[] '[]
  NC :: Cof ki fam y c
     -> ES  ki fam '[] (y ': ys)
     -> EST ki fam '[] (Append (Tyof fam c) tys)
     -> EST ki fam '[] (y ': tys)
  CN :: Cof ki fam x c 
     -> ES  ki fam (x ': xs) '[]
     -> EST ki fam (Append (Tyof fam c) txs) '[]
     -> EST ki fam (x ': txs) '[]
  CC :: Cof ki fam x cx
     -> Cof ki fam y cy
     -> ES ki fam (x ': txs) (y ': tys)
     -> EST ki fam (x ': txs) (Append (Tyof fam cy) tys)
     -> EST ki fam (Append (Tyof fam cx) txs) (y ': tys)
     -> EST ki fam (Append (Tyof fam cx) txs) (Append (Tyof fam cy) tys)
     -> EST ki fam (x ': txs) (y ': tys)
