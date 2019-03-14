{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Examples.TwoThreetree where

import Data.Type.Equality

import Data.Monoid (Sum(..))
import Data.Functor.Const
import Data.GraphViz.Printing
import Data.GraphViz.Types.Monadic
import Data.Proxy
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as IO
import Generics.MRSOP.Base
import qualified Generics.MRSOP.GDiff as GDiff
import Generics.MRSOP.Diff3
import qualified Generics.MRSOP.Diff.Annotate as Annotate
import qualified Generics.MRSOP.Diff.Annotate.Translate as Translate
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util hiding (Cons, Nil)

data Tree a
  = Leaf
  | Two a
        (Tree a)
        (Tree a)
  | Three a
          (Tree a)
          (Tree a)
          (Tree a)
  deriving (Show, Eq)

data TreeKon =
  TreeInt

data TreeSingl (kon :: TreeKon) :: * where
  STreeInt :: Int -> TreeSingl TreeInt

instance Show (TreeSingl k) where
  show (STreeInt x) = show x

deriving instance Eq (TreeSingl k)

instance Show1 TreeSingl where
  show1 = show

instance Eq1 TreeSingl where
  eq1 = (==)

instance TestEquality TreeSingl where
  testEquality (STreeInt _) (STreeInt _) = Just Refl

deriveFamilyWith ''TreeSingl [t|Tree Int|]



t1, t2, t3, t4 :: Tree Int
t1 = Three 1 Leaf (Two 2 Leaf Leaf) (Two 3 Leaf Leaf)

t2 = Three 1 Leaf (Two 5 Leaf Leaf) (Two 3 Leaf Leaf)

t3 = Three 1 Leaf (Two 2 Leaf Leaf) (Three 3 Leaf Leaf Leaf)

t4 = Two 3 Leaf Leaf

t1' = deep @FamTreeInt t1

-- t1Vis = writeFile "t1.dot" (showDot (visualizeFix t1'))
t2' = deep @FamTreeInt t2

-- t2Vis = writeFile "t2.dot" (showDot (visualizeFix t2'))
t3' = deep @FamTreeInt t3

-- t3Vis = writeFile "t3.dot" (showDot (visualizeFix t3'))
t4' = deep @FamTreeInt t4

-- t4Vis = writeFile "t4.dot" (showDot (visualizeFix t4'))
tLong :: Tree Int -> Tree Int
tLong x = Three 1 Leaf (Two 2 Leaf x) Leaf

t1l = tLong t1

t2l = tLong t2

t1l' = deep @FamTreeInt t1l

t2l' = deep @FamTreeInt t2l

type P = Almu TreeSingl CodesTreeInt Z Z

data Outcome
  = FailedA Bool | FailedB Bool | Conflict | Ok | Panic
  deriving Show

willItMerge :: Tree Int -> Tree Int -> Tree Int -> Outcome
willItMerge a o b =
  let a'      = deep @FamTreeInt a
      b'      = deep @FamTreeInt b
      o'      = deep @FamTreeInt o
      oa      = diffTree o a
      ob      = diffTree o b
      on_b'   = mergeAlmu oa ob
      on_a'   = mergeAlmu ob oa
   in case (,) <$> on_a' <*> on_b' of
      Nothing -> Conflict
      Just (ona, onb) ->
        case applyAlmu ona b' of
          Nothing -> FailedA (applyAlmu oa o' == Just a') 
          Just res1 ->
            case applyAlmu onb a' of
              Nothing -> FailedB (applyAlmu ob o' == Just b')
              Just res2 ->
                if eq1 res1 res2
                then Ok
                else Panic

diffTree :: Tree Int -> Tree Int -> P
diffTree o b =
  let b'      = deep @FamTreeInt b
      o'      = deep @FamTreeInt o
      es_ob   = GDiff.diff' o' b'
      es_ob_o = Translate.countCopies $ Annotate.annSrc  o' es_ob
      es_ob_b = Translate.countCopies $ Annotate.annDest b' es_ob
   in Translate.diffAlmu es_ob_o es_ob_b

o1 , a1 , b1 :: Tree Int

o1 = Three 1 (Two 2 Leaf Leaf) (Two 3 Leaf Leaf) Leaf
b1 = Three 1 (Two 2 Leaf Leaf) (Two 30 Leaf Leaf) Leaf
a1 = Three 1 (Two 5 Leaf Leaf) (Two 3 Leaf Leaf) Leaf
         

{-
-- the zipper representation of the tLong function
pLong ::
     Spine TreeSingl CodesTreeInt (Lkup Z CodesTreeInt) 
  -> Almu TreeSingl CodesTreeInt Z
pLong =
  Peel
    (Cons
       (Ctx
          (CS (CS CZ))
          (T (NA_K (STreeInt 1)) $
           T (NA_I (deep Leaf)) $ H (NA_I (deep Leaf) :* NP0)))
       (Cons
          (Ctx
             (CS CZ)
             (T (NA_K (STreeInt 2)) $
              H (NA_I (deep Leaf) :* NP0)))
          Nil))
    Nil

-- don't zip at all
now ::
     Spine TreeSingl CodesTreeInt (Lkup Z CodesTreeInt)
  -> Almu TreeSingl CodesTreeInt Z
now = Peel Nil Nil

p12 :: Almu TreeSingl CodesTreeInt Z
p12 = now p12'

plong12 :: Almu TreeSingl CodesTreeInt Z
plong12 = pLong p12'

p12' :: Spine TreeSingl CodesTreeInt (Lkup Z CodesTreeInt)
p12' =
  (sCns
     (CS (CS CZ))
     (AtSet (Trivial (STreeInt 1) (STreeInt 1)) :* AtFix (now Scp) :*
      AtFix
        (now
           (sCns
              (CS CZ)
              (AtSet (Trivial (STreeInt 2) (STreeInt 5)) :* AtFix (now Scp) :*
               AtFix (now Scp) :*
               NP0))) :*
      AtFix (now Scp) :*
      NP0))
  
-- we can delete subtree and insert with subtree
p13 :: Almu TreeSingl CodesTreeInt Z
p13 =
  let (Fix (Rep (There (Here two)))) =
        deep @FamTreeInt (Two (3 :: Int) Leaf Leaf)
      (Fix (Rep (There (There (Here three))))) =
        deep @FamTreeInt (Three (3 :: Int) Leaf Leaf Leaf)
   in Peel
        Nil
        Nil
        (sCns
           (CS (CS CZ))
           (AtSet (Trivial (STreeInt 1) (STreeInt 1)) :* AtFix (now Scp) :*
            AtFix (now Scp) :*
            AtFix (now (Schg (CS CZ) (CS (CS CZ)) (A0 two three))) :*
            NP0))

-- however, we can be more 'precise' as well
-- we only pinpoint the part that matters, the other leafs are just copied.
-- that is, we're going to change Two to Three, and add a field
p13' :: Almu TreeSingl CodesTreeInt Z
p13' =
  Peel
    Nil
    Nil
    (sCns
       (CS (CS CZ))
       (AtSet (Trivial (STreeInt 1) (STreeInt 1)) :* AtFix (now Scp) :*
        AtFix (now Scp) :*
        AtFix
          (Peel
             Nil
             Nil
             (Schg
                (CS CZ)
                (CS (CS CZ))
                (AX NP0 NP0 (AtSet (Trivial (STreeInt 3) (STreeInt 3))) $
                 AX NP0 NP0 (AtFix (now Scp)) $
                 AX NP0 NP0 (AtFix (now Scp)) $ A0 NP0 (NA_I (deep Leaf) :* NP0)))) :*
        NP0))

p23 :: Almu TreeSingl CodesTreeInt Z
p23 =
  Peel
    Nil
    Nil
    (sCns
       (CS (CS CZ))
       (AtSet (Trivial (STreeInt 1) (STreeInt 1)) :* (AtFix (now Scp)) :*
        (AtFix
           (Peel
              Nil
              Nil
              (sCns
                 (CS (CS CZ))
                 (AtSet (Trivial (STreeInt 5) (STreeInt 2)) :* AtFix (now Scp) :*
                  AtFix (now Scp) :*
                  AtFix (now Scp) :*
                  NP0)))) :*
        (AtFix
           (Peel
              Nil
              Nil
              (Schg
                 (CS CZ)
                 (CS (CS CZ))
                 (AX NP0 NP0 (AtSet (Trivial (STreeInt 1) (STreeInt 1))) $
                  AX NP0 (NA_I (deep Leaf) :* NP0) (AtFix (now Scp)) $
                  AX NP0 NP0 (AtFix (now Scp)) $ A0 NP0 NP0)))) :*
        NP0))
-}
