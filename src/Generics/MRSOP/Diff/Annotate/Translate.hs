{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.Diff.Annotate.Translate where

import Data.Function
import Data.Functor.Const
import Data.Functor.Product
import Data.Monoid (Sum(getSum), (<>))
import Data.Type.Equality
import Generics.MRSOP.AG (monoidAlgebra)
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.Diff.Annotate
import Generics.MRSOP.Util hiding (Cons, Nil)
import Generics.MRSOP.Zipper.Deep

-- | If a given subtree has no more copies, we can only resort
--   to Schg to produce a patch; We call this the stiff patch.
--   In the sense that it completely fixes one element in the
--   domain and one in the image of the application function.
--   This is the worst patch to transform an x into a y.
--
--   One option would be to fall back to the diff algorithm that enumerates
--   all possibilities and choose the one with the least cost.
stiff ::
     (TestEquality ki, IsNat ix)
  => Fix ki codes ix
  -> Fix ki codes ix
  -> Almu ki codes ix
stiff (Fix x) (Fix y) = Peel Nil Nil (stiffS x y)

stiffS :: TestEquality ki =>
     Rep ki (Fix ki codes) xs -> Rep ki (Fix ki codes) xs -> Spine ki codes xs
stiffS x y =
  case (sop x, sop y) of
    (Tag c1 poa1, Tag c2 poa2) ->
      case testEquality c1 c2 of
        (Just Refl) ->
          sCns c1 (mapNP (\(a :*: b) -> stiffAt a b) (zipNP poa1 poa2))
        Nothing -> Schg c1 c2 $ stiffAl poa1 poa2

stiffAt ::
     TestEquality ki
  => NA ki (Fix ki codes) a
  -> NA ki (Fix ki codes) a
  -> At ki codes a
stiffAt (NA_K k1) (NA_K k2) = AtSet (Trivial k1 k2)
stiffAt (NA_I i1) (NA_I i2) = AtFix $ stiff i1 i2

stiffAl ::
     TestEquality ki
  => PoA ki (Fix ki codes) xs
  -> PoA ki (Fix ki codes) ys
  -> Al ki codes xs ys
stiffAl NP0 NP0 = A0 NP0 NP0
stiffAl (x :* xs) NP0 =
  case stiffAl xs NP0 of
    A0 dels inss -> A0 (x :* dels) inss
    AX dels inss at al -> AX (x :* dels) inss at al
stiffAl NP0 (y :* ys) =
  case stiffAl NP0 ys of
    A0 dels inss -> A0 dels (y :* inss)
    AX dels inss at al -> AX dels (y :* inss) at al
stiffAl (x :* xs) (y :* ys) =
  case testEquality x y of
    Just Refl -> AX NP0 NP0 (stiffAt x y) (stiffAl xs ys)
    Nothing ->
      case stiffAl xs ys of
        A0 dels inss -> A0 (x :* dels) (y :* inss)
        AX dels inss at al -> AX (x :* dels) (y :* inss) at al

-- utility function to extract an annotation 
extractAnn :: NA ki (AnnFix ki codes phi) ('I ix) -> phi ix
extractAnn (NA_I (AnnFix ann _)) = ann

diffAl ::
     TestEquality ki
  => PoA ki (AnnFix ki codes (Const Ann)) xs
  -> PoA ki (AnnFix ki codes (Const Ann)) ys
  -> Al ki codes xs ys
diffAl NP0 NP0 = A0 NP0 NP0
diffAl NP0 ys = undefined
diffAl xs NP0 = undefined
diffAl (x :* xs) (y :* ys) =
  let al = diffAl xs ys
   in case (x, y) of
        (NA_K k1, NA_K k2) ->
          case testEquality k1 k2 of
            Just Refl -> AX NP0 NP0 (diffAt x y) al
            Nothing ->
              case al of
                A0 dels inss ->
                  A0
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                AX dels inss at al ->
                  AX
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                    at
                    al
        (NA_K k1, NA_I i2) ->
          case getConst . extractAnn $ y of
            Modify ->
              case al of
                A0 dels inss -> 
                  undefined
                  {- A0
                    dels
                    -- TODO: Victor Victor! Here we're stuck in a scary way too!
                    (mapNA id forgetAnn y :* inss)
                    -}
                AX dels inss at al -> undefined
                  {-AX
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                    at
                    al-}
            Copy -> 
              case al of
                A0 dels inss -> undefined
                  {-A0
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss) -}
                AX dels inss at al -> undefined
                  {-AX
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                    at
                    al-}
        (NA_I i1, NA_K k2) ->
          case getConst . extractAnn $ x of
            Modify ->
              case al of
                A0 dels inss -> undefined
                  {-A0
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss) -}
                AX dels inss at al -> undefined
                  {-AX
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                    at
                    al-}
            Copy ->
              case al of
                A0 dels inss -> undefined
                  {-A0
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss) -}
                AX dels inss at al -> undefined
                  {-AX
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                    at
                    al-}
        (NA_I i1, NA_I i2) ->
          -- TODO the trick here is to  testEquality x y 
          case (getConst . extractAnn $ x, getConst . extractAnn $ y) of
            (Modify, _) -> 
              case al of
                A0 dels inss -> undefined
                  {-A0
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss) -}
                AX dels inss at al -> undefined
                  {-AX
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                    at
                    al-}
            (Copy, Modify) -> 
              case al of
                A0 dels inss -> undefined
                  {-A0
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss) -}
                AX dels inss at al -> undefined
                  {-AX
                    (mapNA id forgetAnn x :* dels)
                    (mapNA id forgetAnn y :* inss)
                    at
                    al-}

            -- TODO: Victor! Victor! Here we are in Trouble!
            -- we can't continue because i1 and i2
            -- point to different parts in the family!
            -- i2 :: AnnFix ki codes (Const Ann) iy
            -- i1 :: AnnFix ki codes (Const Ann) ix
            --
            -- In the agda code this wasn't a problem, due
            -- to the assumption that the datatype is regular...
            (Copy, Copy) -> undefined -- AX NP0 NP0 (diffAt x y) al
diffAt ::
     NA ki (AnnFix ki codes (Const Ann)) a
  -> NA ki (AnnFix ki codes (Const Ann)) a
  -> At ki codes a
diffAt = undefined

diffSpine ::
     (TestEquality ki, Eq1 ki)
  => Rep ki (AnnFix ki codes (Const Ann)) xs
  -> Rep ki (AnnFix ki codes (Const Ann)) xs
  -> Spine ki codes xs
diffSpine s1 s2 =
  if (eq1 `on` mapRep forgetAnn) s1 s2
    then Scp
    else case (sop s1, sop s2) of
           (Tag c1 p1, Tag c2 p2) ->
             case testEquality c1 c2 of
               Just Refl ->
                 sCns c1 (mapNP (\(a :*: b) -> diffAt a b) (zipNP p1 p2))
               Nothing -> Schg c1 c2 (diffAl p1 p2)


countCopies :: AnnFix ki codes (Const Ann) ix -> Int
countCopies = getSum . getConst . annCata copiesAlgebra
  where
    copiesAlgebra (Const Copy) = (Const 1 <>) . monoidAlgebra
    copiesAlgebra _ = monoidAlgebra

diffDel ::
     Rep ki (AnnFix ki codes (Const Ann)) (Lkup ix codes)
  -> AnnFix ki codes (Const Ann) ix
  -> Almu ki codes ix
diffDel r x = undefined

-- | Takes two annotated trees, and produces a patch
--
--  TODO: Because we have the two zippers ,we need to
--  be a bit smarter than diff-del, diff-ins
--
--  I'm not fully understanding the Agda code, and
--  how we would reproduce it here.
diffAlmu ::
     (IsNat ix, TestEquality ki)
  => AnnFix ki codes (Const Ann) ix
  -> AnnFix ki codes (Const Ann) ix
  -> Almu ki codes ix
diffAlmu fx@(AnnFix (Const Modify) x) fy@(AnnFix (Const Modify) y) =
  if countCopies fx > 0
    then diffDel x fy
    else (stiff `on` Fix . mapRep forgetAnn) x y
diffAlmu fx@(AnnFix (Const Modify) x) (AnnFix (Const Copy) y) =
  if countCopies fx > 0
    then undefined
    else (stiff `on` Fix . mapRep forgetAnn) x y
diffAlmu (AnnFix (Const Copy) x) fy@(AnnFix (Const Modify) y) =
  if countCopies fy > 0
    then undefined
    else (stiff `on` Fix . mapRep forgetAnn) x y
diffAlmu (AnnFix (Const Copy) x) (AnnFix (Const Copy) y) = undefined
