{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | For the lack of a better name, here we put random stuff
module Generics.MRSOP.GDiff.Util where

import Generics.MRSOP.Base hiding (listPrfNP)
import Generics.MRSOP.Util ((:++:))


-- |An inhabitant of @ListPrf ls@ is *not* a singleton!
--  It only proves that @ls@ is, in fact, a type level list.
--  This is useful since it enables us to pattern match on
--  type-level lists whenever we see fit.
data ListPrf :: [k] -> * where
  Nil ::  ListPrf '[]
  Cons :: ListPrf l ->  ListPrf (x ': l)

-- |The @IsList@ class allows us to construct
--  'ListPrf's in a straight forward fashion.
class IsList (xs :: [k]) where
  listPrf :: ListPrf xs
instance IsList '[] where
  listPrf = Nil
instance IsList xs => IsList (x ': xs) where
  listPrf = Cons listPrf

-- |Concatenation of lists is also a list.
appendIsListLemma :: ListPrf xs -> ListPrf ys -> ListPrf (xs :++: ys)
appendIsListLemma Nil         isys = isys
appendIsListLemma (Cons isxs) isys = Cons (appendIsListLemma isxs isys)

-- |Convenient constraint synonyms
type L1 xs          = (IsList xs) 
type L2 xs ys       = (IsList xs, IsList ys) 
type L3 xs ys zs    = (IsList xs, IsList ys, IsList zs) 
type L4 xs ys zs as = (IsList xs, IsList ys, IsList zs, IsList as) 

data RList :: [k] -> * where
  RList :: IsList ts => RList ts

-- this seems more like "Coerce" to me
{-# INLINE reify #-}
reify :: ListPrf ts -> RList ts
reify Nil = RList
reify (Cons x) = case reify x of RList -> RList



-- |Proves that the index of a value of type 'NP' is a list.
--  This is useful for pattern matching on said list without
--  having to carry the product around.
listPrfNP :: NP p xs -> ListPrf xs
listPrfNP NP0       = Nil
listPrfNP (_ :* xs) = Cons $ listPrfNP xs
