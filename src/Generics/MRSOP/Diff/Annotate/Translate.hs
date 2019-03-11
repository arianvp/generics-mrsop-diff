{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.Diff.Annotate.Translate where

import Control.Arrow
import Data.Foldable (fold)
import Data.Function
import Debug.Trace
import Data.Proxy
import Data.List (maximumBy, zip)
import Data.Ord (comparing)
import Data.Functor.Const
import Data.Functor.Product
import Data.Maybe (fromJust)
import Data.Monoid
  ( First(First, getFirst)
  , Last(Last, getLast)
  , Sum(Sum, getSum)
  )
import Data.Semigroup (Max(Max, getMax), (<>))
import Data.Type.Equality
import Generics.MRSOP.AG (mapAnn, monoidAlgebra, synthesizeAnn, productAnn)
import Generics.MRSOP.Base
import Generics.MRSOP.Diff.Annotate
import Generics.MRSOP.Diff3
import Generics.MRSOP.Util hiding (Cons, Nil)
import Unsafe.Coerce (unsafeCoerce)

-- | TODO make something nicer, maybe a table
showDatatypeName :: DatatypeName -> String
showDatatypeName (Name str) = str
showDatatypeName (x :@: y) =
  showDatatypeName x ++ "(" ++ showDatatypeName y ++ ")"

-- | Stiff diff is the worst diff we can make from ix to iy
--
-- We do this by deleting   ix, and inserting iy


-- utility function to extract an annotation 
extractAnn :: NA ki (AnnFix ki codes phi) ('I ix) -> phi ix
extractAnn (NA_I (AnnFix ann _)) = ann

-- | Little helper
forgetAnn' = mapNA id forgetAnn

-- TODO / NOTE: fromJust because we know copiesAlgebra always Annotates leaves with a First.
-- it's the First Semigroup, not the First Monoid. But haskell doesn't distinguish between
-- the two. We could add our own datatype later.
diffAl :: forall ki fam codes xs ys.
     (Eq1 ki, TestEquality ki)
  => PoA ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) xs
  -> PoA ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) ys
  -> Al ki codes xs ys
diffAl NP0 NP0 = A0
diffAl NP0 (y :* ys) = AIns (mapNA id forgetAnn y) (diffAl NP0 ys)
diffAl (x :* xs) NP0 = ADel (mapNA id forgetAnn x) (diffAl xs NP0)
diffAl (x@(NA_K k1) :* xs) (y@(NA_K k2) :* ys) = 
  case testEquality k1 k2 of
    Just Refl -> AX (diffAt x y) (diffAl xs ys)
    Nothing -> AIns (mapNA id forgetAnn y) (ADel (mapNA id forgetAnn x) (diffAl xs ys))
diffAl (x@(NA_K k1) :* xs) (y@(NA_I i2) :* ys) = 
  case getAnn' (extractAnn y) of
    Modify -> AIns (mapNA id forgetAnn y) (diffAl (x :* xs) ys)
    Copy -> ADel (mapNA id forgetAnn x) (diffAl xs (y :* ys))
diffAl (x@(NA_I i1) :* xs) (y@(NA_K k2) :* ys) =
  case getAnn' (extractAnn x) of
    Modify -> ADel (mapNA id forgetAnn x) (diffAl xs (y :* ys))
    Copy -> AIns (mapNA id forgetAnn y) (diffAl (x :* xs) ys)
diffAl (x@(NA_I i1) :* xs) (y@(NA_I i2) :* ys) = 
  case (getAnn' (extractAnn x), getAnn' (extractAnn y)) of
    (Modify, _) -> ADel (mapNA id forgetAnn x) (diffAl xs (y :* ys))
    (Copy, Modify) -> AIns (mapNA id forgetAnn y) (diffAl (x :* xs) ys)
    (Copy, Copy) -> 
      case testEquality x y of
        Just Refl -> AX (diffAt x y) (diffAl xs ys)
        -- NOTE we added this case
        Nothing -> AIns (mapNA id forgetAnn y) (ADel (mapNA id forgetAnn x) (diffAl xs ys))


diffAt ::
     (Eq1 ki, TestEquality ki)
  => NA ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) a
  -> NA ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) a
  -> At ki codes a
diffAt (NA_K x) (NA_K y) = AtSet (Trivial x y)
diffAt (NA_I x) (NA_I y) = AtFix $ diffAlmu x y

diffSpine :: forall ki codes ix iy.
     (TestEquality ki, Eq1 ki, IsNat ix, IsNat iy)
  => SNat ix -- needed so we can decide what family we're in
  -> SNat iy
  -> Rep ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) (Lkup ix codes)
  -> Rep ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) (Lkup iy codes)
  -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
diffSpine six siy s1@(sop -> Tag c1 p1) s2@(sop -> Tag c2 p2) =
  case testEquality six siy of
    Just Refl ->
      if (eq1 `on` mapRep forgetAnn) s1 s2
        then Scp
        else case testEquality c1 c2 of
                   Just Refl ->
                     SCns c1 (mapNP (\(a :*: b) -> diffAt a b) (zipNP p1 p2))
                   Nothing -> SChg c1 c2 (diffAl p1 p2)
    Nothing -> SChg c1 c2 (diffAl p1 p2)

copiesAlgebra
  :: Const Ann ix
  -> Rep ki (Const (Sum Int)) xs
  -> Const (Sum Int) ix
copiesAlgebra (Const Copy) = (Const 1 <>) . monoidAlgebra
copiesAlgebra (Const Modify) = monoidAlgebra

-- annotates the tree with how many copies are underneath each node
-- (inclusive with self)
-- copies Copy = 1 + copies children
-- copies Modify = copies children
countCopies
  :: IsNat ix
  => AnnFix ki codes (Const Ann) ix
  -> AnnFix ki codes (Product (Const (Sum Int)) (Const Ann)) ix
countCopies = synthesizeAnn (productAnn copiesAlgebra const)

-- TODO: Discuss with Victor
-- A maximum path of copies  should always in the same index, correct?
-- We alternative until we get there. However, this is not the case now :(
diffCtx
  :: forall ki fam codes p ix xs.  
     (Eq1 ki, TestEquality ki, IsNat ix) => 
     InsOrDel ki codes p
  -> AnnFix ki codes (Product (Const (Sum Int)) (Const Ann)) ix
  -> PoA ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) xs
  -> Ctx ki codes p ix xs
diffCtx cid x xs
 = 
  let maxIdx = fst max
      max = maximumBy (comparing snd) zipped
      zipped = zip [0 .. ] elimmed
      elimmed = elimNP (elimNA (const 0) (getCopies . getAnn)) xs
      drop' ::
           Int
        -> PoA ki (AnnFix ki codes (Product (Const (Sum Int)) (Const Ann))) ys
        -> Ctx ki codes p ix ys
      drop' n NP0 = error "We should've found it"
      drop' 0 (NA_I y :* ys) =
        case cid of
          CtxIns ->
            H (diffAlmu x y) (mapNP forgetAnn' ys)
          CtxDel ->
            H (AlmuMin (diffAlmu y x)) (mapNP forgetAnn' ys)
      drop' n (y :* ys) = T (forgetAnn' y) (drop' (n - 1) ys)
   in drop' maxIdx xs

extractNat :: forall ki phi n. NA ki phi (I n) -> Integer
extractNat (NA_I _) = getNat (Proxy :: Proxy n)

getCopies :: Product (Const (Sum Int)) chi ix -> Int
getCopies (Pair (Const (Sum a)) _) = a

getAnn' :: Product phi (Const Ann) ix -> Ann
getAnn' (Pair _ (Const b)) = b

hasCopies :: AnnFix ki codes (Product (Const (Sum Int)) chi) ix -> Bool
hasCopies (AnnFix (Pair (Const (Sum x)) _) _) = x > 0 -- | Takes two annotated trees, and produces a patch

stiffAlmu :: (TestEquality ki, Eq1 ki) => Fix ki codes ix -> Fix ki codes iy -> Almu ki codes ix iy
stiffAlmu (Fix rep1) (Fix rep2) = Spn (stiffSpine rep1 rep2)

stiffSpine :: (TestEquality ki, Eq1 ki)
  => Rep ki (Fix ki codes) xs
  -> Rep ki (Fix ki codes) ys
  -> Spine ki codes xs ys
stiffSpine (sop -> Tag c1 p1) (sop -> Tag c2 p2) = SChg c1 c2 (stiffAl p1 p2)

stiffAt :: (TestEquality ki, Eq1 ki) => NA ki (Fix ki codes) x -> NA ki (Fix ki codes) x -> At ki codes x
stiffAt (NA_K x) (NA_K y) = AtSet (Trivial x y)
stiffAt (NA_I x) (NA_I y) = AtFix (stiffAlmu x y)

stiffAl :: (TestEquality ki, Eq1 ki) => PoA ki (Fix ki codes) xs -> PoA ki (Fix ki codes) ys -> Al ki codes xs ys
stiffAl NP0 NP0 = A0
stiffAl (x :* xs) NP0 = ADel x (stiffAl xs NP0)
stiffAl NP0 (y :* ys) = AIns y (stiffAl NP0 ys)
stiffAl (x :* xs) (y :* ys) = 
  case testEquality x y of
    Just Refl -> AX (stiffAt x y) (stiffAl xs ys)
    Nothing -> AIns y (ADel x (stiffAl xs ys))

diffAlmu :: forall ki fam codes ix iy.
     (Eq1 ki, IsNat ix, IsNat iy, TestEquality ki)
  => AnnFix ki codes (Product (Const (Sum Int)) (Const Ann)) ix
  -> AnnFix ki codes (Product (Const (Sum Int)) (Const Ann)) iy
  -> Almu ki codes ix iy
diffAlmu x@(AnnFix ann1 rep1) y@(AnnFix ann2 rep2) =
  case (getAnn' ann1, getAnn' ann2) of
    (Copy, Copy) -> Spn (diffSpine (getSNat $ Proxy @ix) (getSNat $ Proxy @iy) rep1 rep2)
    (Copy, Modify) -> 
      if hasCopies y then diffIns x rep2 else stiffAlmu (forgetAnn x) (forgetAnn y)
    (Modify, Copy) ->
      if hasCopies x then diffDel rep1 y else stiffAlmu (forgetAnn x) (forgetAnn y)
    (Modify, Modify) ->
      if hasCopies x then diffDel rep1 y else stiffAlmu (forgetAnn x) (forgetAnn y)
    where
      diffIns x rep = case sop rep of Tag c xs -> Ins c (diffCtx CtxIns x xs)
      diffDel rep x = case sop rep of Tag c xs -> Del c (diffCtx CtxDel x xs)

