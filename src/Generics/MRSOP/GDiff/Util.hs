{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | For the lack of a better name, here we put random stuff
module Generics.MRSOP.GDiff.Util where

import Generics.MRSOP.Base

-- | Appends two type level lists
type family Append (txs :: [k]) (tys :: [k]) :: [k] where
  Append '[] tys = tys
  Append (tx ': txs) tys = tx ': (Append txs tys)



data ListPrf :: [k] -> * where
  Nil ::  ListPrf '[]
  Cons :: ListPrf l ->  ListPrf (x ': l)

class IsList (xs :: [k]) where
  isList :: ListPrf xs

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

data Trivial :: k -> * where
  MkTrivial :: Trivial k

-- We can have some kind of forgetful functor that ignores p
npToListPrf :: NP p xs -> ListPrf xs
npToListPrf NP0       = Nil
npToListPrf (_ :* xs) = Cons (npToListPrf xs)

-- we can go the other way around. not sure if useful
listPrfToNP :: ListPrf xs -> NP Trivial xs
listPrfToNP Nil = NP0
listPrfToNP (Cons xs) = MkTrivial :* listPrfToNP xs

