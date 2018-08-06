{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

-- Annotates a source an destination tree
-- by zipping a 'GDiff' patch with a Fix
module Generics.MRSOP.Diff.Annotate where

import Data.Coerce
import Data.Functor.Const
import Generics.MRSOP.Base
import Generics.MRSOP.GDiff
import Generics.MRSOP.Util

import Data.Maybe (fromJust)

-- | Annotations for each family in the datatype
-- we ignore ix, as they're the same everywhere
data Ann = Modify | Copy deriving Show


injCofAnn ::
     Cof ki codes a c
  -> Const ann ix
  -> PoA ki (AnnFix ki codes (Const ann)) (Tyof codes c)
  -> NA ki (AnnFix ki codes (Const ann)) a
injCofAnn (ConstrI c) ann xs =
    -- And here we are stuck
    --
    -- We have an ann :: Const ann ix
    --
    -- but we need to produce an   _ :: Const ann n
    -- 
    -- However, we know that Const discards the second argument,
    -- so they are actually equal!
    --
    -- We can use coerce as  Const is coercible
    --
    NA_I (AnnFix (coerce ann) $ inj c xs)

    where
      constToConst = Const . getConst
injCofAnn (ConstrK k) ann xs = NA_K k

-- lemma needed for inserting an annotation at the place of 
-- a constructor
insCofAnn ::
     Cof ki codes a c
  -> Const ann ix
  -> ListPrf (Tyof codes c)
  -> PoA ki (AnnFix ki codes (Const ann)) (Tyof codes c :++: as)
  -> PoA ki (AnnFix ki codes (Const ann)) (a ': as)
insCofAnn c ann prf xs =
  let (xs0, xs1) = split prf xs
   in injCofAnn c ann xs0 :* xs1

{-
 - In Agda, it would be the following. However, I'm not sure
 - it is possible to carry around the IsJust constraint in Haskell
 - hence, we will be partial instead
 -  ann-source : ∀{txs tys}(xs : ⟦ txs ⟧A*)(p : ES txs tys)
 -           → (hip : IsJust (applyES p xs))
 -           → ⟦ txs ⟧Aₐ*
 -
 - However, it's morally total if you know beforehand that the
 - patch is gonna apply. Which we know by construction everywhere we use this
 - , so we can just `fromJust` it where appropriate
 -
 - WARNING: Morally dubious, but we know that this edit script was
 - generated hte same time as the datatype, so it should never
 - fail to apply
 -
 - TODO: Actually make it return Maybe and be honest
 -}
annSrc ::
     Eq1 ki
  => PoA ki (Fix ki codes) xs
  -> ES ki codes xs ys
  -> PoA ki (AnnFix ki codes (Const Ann)) xs
annSrc xs ES0 = NP0
annSrc xs (Ins c es) = annSrc xs es
annSrc (x :* xs) (Del c es)
 =
  let poa = fromJust $ matchCof c x
   in insCofAnn c (Const Modify) listPrf (annSrc (appendNP poa xs) es)
annSrc (x :* xs) (Cpy c es) =
  let poa = fromJust $ matchCof c x
   in insCofAnn c (Const Copy) listPrf (annSrc (appendNP poa xs) es)

annDest ::
     Eq1 ki
  => PoA ki (Fix ki codes) ys
  -> ES ki codes xs ys
  -> PoA ki (AnnFix ki codes (Const Ann)) ys
annDest xs ES0 = NP0
annDest xs (Del c es) = annDest xs es
annDest (x :* xs) (Ins c es)
 =
  let poa = fromJust $ matchCof c x
   in insCofAnn c (Const Modify) listPrf (annDest (appendNP poa xs) es)
annDest (x :* xs) (Cpy c es) =
  let poa = fromJust $ matchCof c x
   in insCofAnn c (Const Copy) listPrf (annDest (appendNP poa xs) es)
