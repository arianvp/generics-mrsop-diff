{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Generics.MRSOP.AG (mapAnn, monoidAlgebra, synthesizeAnn)
import Generics.MRSOP.Base
import Generics.MRSOP.Diff.Annotate
import Generics.MRSOP.Diff2
import Generics.MRSOP.Util hiding (Cons, Nil)
import Unsafe.Coerce (unsafeCoerce)

-- | If a given subtree has no more copies, we can only resort
--   to Schg to produce a patch; We call this the stiff patch.
--   In the sense that it completely fixes one element in the
--   domain and one in the image of the application function.
--   This is the worst patch to transform an x into a y.
--
--   One option would be to fall back to the diff algorithm that enumerates
--   all possibilities and choose the one with the least cost.
stiff ::
     (TestEquality ki, IsNat ix, IsNat iy)
  => Fix ki codes ix
  -> Fix ki codes iy
  -> Almu ki codes ix iy
stiff (Fix x) (Fix y) = undefined
  {- case (sop x, sop y) of
    (Tag c1 xs, Tag c2 ys) -> 
      Del c1 (DH _ xs) -- (stiffS x y) -}

stiffS ::
     TestEquality ki
  => Rep ki (Fix ki codes) xs
  -> Rep ki (Fix ki codes) xs
  -> Spine ki codes xs
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

-- | Little helper
forgetAnn' = mapNA id forgetAnn

-- TODO / NOTE: fromJust because we know copiesAlgebra always Annotates leaves with a First.
-- it's the First Semigroup, not the First Monoid. But haskell doesn't distinguish between
-- the two. We could add our own datatype later.
diffAl ::
     (Show1 ki, Eq1 ki, TestEquality ki)
  => PoA ki (AnnFix ki codes (Const (Sum Int, First Ann))) xs
  -> PoA ki (AnnFix ki codes (Const (Sum Int, First Ann))) ys
  -> Al ki codes xs ys
diffAl NP0 NP0 = A0 NP0 NP0
diffAl NP0 (y :* ys) =
  case diffAl NP0 ys of
    A0 dels inss -> A0 dels (forgetAnn' y :* inss)
    AX dels inss at al -> AX dels (forgetAnn' y :* inss) at al
diffAl (x :* xs) NP0 =
  case diffAl xs NP0 of
    A0 dels inss -> A0 (forgetAnn' x :* dels) inss
    AX dels inss at al -> AX (forgetAnn' x :* dels) inss at al
diffAl (x :* xs) (y :* ys) =
  case (x, y, testEquality x y) of
    (NA_K k1, NA_K k2, Just Refl) -> AX NP0 NP0 (diffAt x y) (diffAl xs ys)
    (NA_K k1, NA_K k2, Nothing) ->
      case diffAl xs ys of
        A0 dels inss -> A0 (forgetAnn' x :* dels) (forgetAnn' y :* inss)
        AX dels inss at al ->
          AX (forgetAnn' x :* dels) (forgetAnn' y :* inss) at al
    (NA_K k1, NA_I i2, Nothing) ->
      case fromJust . getAnn' . extractAnn $ y of
        Modify ->
          case diffAl (x :* xs) ys of
            A0 dels inss -> A0 dels (forgetAnn' y :* inss)
            AX dels inss at al -> AX dels (forgetAnn' y :* inss) at al
        Copy ->
          case diffAl xs (y :* ys) of
            A0 dels inss -> A0 (forgetAnn' x :* dels) inss
            AX dels inss at al -> AX (forgetAnn' x :* dels) inss at al
    (NA_I i1, NA_K k2, Nothing) ->
      case fromJust . getAnn' . extractAnn $ x of
        Modify ->
          case diffAl xs (y :* ys) of
            A0 dels inss -> A0 (forgetAnn' x :* dels) inss
            AX dels inss at al -> AX (forgetAnn' x :* dels) inss at al
        Copy ->
          case diffAl (x :* xs) ys of
            A0 dels inss -> A0 dels (forgetAnn' y :* inss)
            AX dels inss at al -> AX dels (forgetAnn' y :* inss) at al
    (NA_I i1, NA_I i2, Just Refl) ->
      case ( fromJust . getAnn' . extractAnn $ x
           , fromJust . getAnn' . extractAnn $ y) of
        (Modify, _) ->
          case diffAl xs (y :* ys) of
            A0 dels inss -> A0 (forgetAnn' x :* dels) inss
            AX dels inss at al -> AX (forgetAnn' x :* dels) inss at al
        (Copy, Modify) ->
          case diffAl (x :* xs) ys of
            A0 dels inss -> A0 dels (forgetAnn' y :* inss)
            AX dels inss at al -> AX dels (forgetAnn' y :* inss) at al
        (Copy, Copy) -> AX NP0 NP0 (diffAt x y) (diffAl xs ys)

    -- Haskell doesn't allow us to discharge contradictions unfortunately, so it gets confused
    (NA_I i1, NA_K k2, Just a) -> error "absurd.  This is a contradiction. NA_I != NA_K"
    (NA_K k1, NA_I i2, Just b) -> error "absurd. This is a contradiction. NA_K != NA_I"
    (NA_I i1, NA_I i2, Nothing) ->
      case ( fromJust . getAnn' . extractAnn $ x
           , fromJust . getAnn' . extractAnn $ y) of
        (Copy, Copy) -> error "HELP HELP. I don't know if this ever occurs"
        (Modify, _) ->
          case diffAl xs (y :* ys) of
            A0 dels inss -> A0 (forgetAnn' x :* dels) inss
            AX dels inss at al -> AX (forgetAnn' x :* dels) inss at al
        (Copy, Modify) ->
          case diffAl (x :* xs) ys of
            A0 dels inss -> A0 dels (forgetAnn' y :* inss)
            AX dels inss at al -> AX dels (forgetAnn' y :* inss) at al

diffAt ::
     (Show1 ki, Eq1 ki, TestEquality ki)
  => NA ki (AnnFix ki codes (Const (Sum Int, First Ann))) a
  -> NA ki (AnnFix ki codes (Const (Sum Int, First Ann))) a
  -> At ki codes a
diffAt (NA_K x) (NA_K y) = AtSet (Trivial x y)
diffAt (NA_I x) (NA_I y) = AtFix $ diffAlmu x y

diffSpine ::
     (TestEquality ki, Show1 ki, Eq1 ki)
  => Rep ki (AnnFix ki codes (Const (Sum Int, First Ann))) xs
  -> Rep ki (AnnFix ki codes (Const (Sum Int, First Ann))) xs
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

{-
copiesAlgebra (Const Copy) = (Const 1 <>) . monoidAlgebra
copiesAlgebra _ = monoidAlgebra
-}
-- annotates the tree with how many copies are underneath each node
-- (inclusive with self)
-- copies Copy = 1 + copies children
-- copies Modify = copies children
copiesAlgebra ::
     Const Ann iy
  -> Rep ki (Const (Sum Int, First Ann)) xs
  -> Const (Sum Int, First Ann) iy
copiesAlgebra (Const Copy) = (Const (1, First $ Just Copy) <>) . monoidAlgebra
copiesAlgebra (Const Modify) =
  (Const (mempty, First $ Just $ Modify) <>) . monoidAlgebra

countCopies ::
     AnnFix ki codes (Const Ann) ix
  -> AnnFix ki codes (Const (Sum Int, First Ann)) ix
countCopies = synthesizeAnn copiesAlgebra

data CtxInsDel
  = CtxIns
  | CtxDel
  deriving Show

{-diffCtx ::
     forall ki ix codes xs. (Show1 ki, Eq1 ki, TestEquality ki, IsNat ix)
  => CtxInsDel
  -> AnnFix ki codes (Const (Sum Int, First Ann)) ix
  -> PoA ki (AnnFix ki codes (Const (Sum Int, First Ann))) xs
  -> Ctx ki codes ix xs
diffCtx cid x xs
 = 
  let maxIdx = fst max
      max = maximumBy (comparing snd) zipped
      zipped = zip [0 .. ] elimmed
      elimmed = elimNP (elimNA (const 0) (getSum . fst . getConst . getAnn)) xs
      drop' ::
           Int
        -> PoA ki (AnnFix ki codes (Const (Sum Int, First Ann))) ys
        -> Ctx ki codes ix ys
      drop' n NP0 = error "We should've found it"
      drop' 0 (y :* ys) =
        -- TODO: there is a bug here.
        --
        -- At first, I converted  ALmu to a homogenous form by using
        -- normal form contexts. However, I went back to the old definition
        -- of Almu such that the code here was easily portable from Agda.
        -- As it's kind a difficult to build up Ctxs stack programatically, or
        -- at least, I didn't find it straightforward.  However, when doing so
        -- I forgot to make Almu heterogenous agian, making it impossible to
        -- change the _index_ into the family. Hence we can not diff 
        -- an Expr with a Stmt at the moment. Which is a bug :)
        case (testEquality (NA_I x) y, y) of
          (Just Refl, NA_I y) ->
            H (case cid of
                 CtxIns -> diffAlmu x y
                 CtxDel -> diffAlmu y x)
            (mapNP forgetAnn' ys)
          (Nothing, NA_I _) ->
            error $ "we want to change  " ++ show (extractNat (NA_I x)) ++ " into " ++ show (extractNat y)
                  
      drop' n (y :* ys) = T (forgetAnn' y) (drop' (n - 1) ys)
   in drop' maxIdx xs
-}

extractNat :: forall ki phi n. NA ki phi (I n) -> Integer
extractNat (NA_I _) = getNat (Proxy :: Proxy n)

diffInsCtx
  :: AnnFix ki codes (Const (Sum Int, First ann)) ix
  -> PoA ki (AnnFix ki codes (Const (Sum Int, First Ann))) xs
  -> InsCtx ki codes ix xs
diffInsCtx = undefined
diffIns ::
     (Show1 ki, Eq1 ki, TestEquality ki, IsNat ix)
  => AnnFix ki codes (Const (Sum Int, First Ann)) ix
  -> Rep ki (AnnFix ki codes (Const (Sum Int, First Ann))) (Lkup ix codes)
  -> Almu ki codes ix ix
diffIns x rep =
  case sop rep of
    -- Euh what happens if xs is NP0 here, i.e. a leaf
    Tag c NP0 -> undefined -- stiff (forgetAnn x) (Fix (mapRep forgetAnn rep))
    Tag c xs -> Ins c (diffInsCtx x xs)

diffDel ::
     (Show1 ki, Eq1 ki, TestEquality ki, IsNat ix)
  => Rep ki (AnnFix ki codes (Const (Sum Int, First Ann))) (Lkup ix codes)
  -> AnnFix ki codes (Const (Sum Int, First Ann)) iy
  -> Almu ki codes ix iy
diffDel rep x =
  case sop rep of
    Tag c NP0 -> undefined -- stiff (forgetAnn x) (Fix (mapRep forgetAnn rep))
    Tag c xs -> Del c (diffCtx CtxDel x xs)

getAnn' :: (Const (Sum Int, First Ann) ix) -> Maybe Ann
getAnn' (Const (_, First x)) = x

hasCopies :: AnnFix ki codes (Const (Sum Int, First Ann)) ix -> Bool
hasCopies (AnnFix (Const (Sum x, _)) _) = x > 0

-- | Takes two annotated trees, and produces a patch
diffAlmu ::
     (Show1 ki, Eq1 ki, IsNat ix, TestEquality ki)
  => AnnFix ki codes (Const (Sum Int, First Ann)) ix
  -> AnnFix ki codes (Const (Sum Int, First Ann)) iy
  -> Almu ki codes ix iy
diffAlmu x@(AnnFix ann1 rep1) y@(AnnFix ann2 rep2) =
  case (fromJust $ getAnn' $ ann1, fromJust $ getAnn' $ ann2) of
    (Copy, Copy) -> Spn (diffSpine rep1 rep2)
    (Copy, Modify) -> 
      if hasCopies y
        then diffIns x rep2
        else stiff (forgetAnn x) (forgetAnn y)
    (Modify, Copy) -> diffDel rep1 y
    (Modify, Modify) ->
      if hasCopies x
        then diffDel rep1 y
        else stiff (forgetAnn x) (forgetAnn y)
