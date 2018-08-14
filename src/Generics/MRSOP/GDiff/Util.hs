{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | For the lack of a better name, here we put random stuff
module Generics.MRSOP.GDiff.Util where

import Generics.MRSOP.Base
import Generics.MRSOP.Util

data RList :: [k] -> * where
  RList :: IsList ts => RList ts

-- this seems more like "Coerce" to me
{-# INLINE reify #-}
reify :: ListPrf ts -> RList ts
reify Nil = RList
reify (Cons x) = case reify x of RList -> RList

data Trivial :: k -> * where
  MkTrivial :: Trivial k

-- we can go the other way around. not sure if useful
listPrfToNP :: ListPrf xs -> NP Trivial xs
listPrfToNP Nil = NP0
listPrfToNP (Cons xs) = MkTrivial :* listPrfToNP xs
