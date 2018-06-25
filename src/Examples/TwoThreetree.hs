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

module Examples.TwoThreetree where

import Data.Type.Equality

import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.GraphViz.Deep
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import qualified Generics.MRSOP.Zipper as Zipper

data Tree a
  = Leaf
  | Two a
        (Tree a)
        (Tree a)
  | Three a
          (Tree a)
          (Tree a)
          (Tree a)
  deriving (Show)

data TreeKon =
  TreeInt

data TreeSingl (kon :: TreeKon) :: * where
  STreeInt :: Int -> TreeSingl TreeInt

deriving instance Show (TreeSingl k)

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
p12 :: Almu TreeSingl FamTreeInt CodesTreeInt Z
p12 =
  Peel
    (Proxy :: Proxy Z)
    Zipper.Nil
    Zipper.Nil
    (sCns
       (CS (CS CZ))
       (AtSet (Trivial (STreeInt 1) (STreeInt 1)) :*
        AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
        AtFix
          (Peel
             (Proxy :: Proxy Z)
             Zipper.Nil
             Zipper.Nil
             (sCns
                (CS CZ)
                (AtSet (Trivial (STreeInt 2) (STreeInt 5)) :*
                 AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
                 AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
                 NP0))) :*
        AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
        NP0))

-- we can delete subtree and insert with subtree
p13 :: Almu TreeSingl FamTreeInt CodesTreeInt Z
p13 =
  let (Fix (Rep (There (Here two)))) =
        deep @FamTreeInt (Two (3 :: Int) Leaf Leaf)
      (Fix (Rep (There (There (Here three))))) =
        deep @FamTreeInt (Three (3 :: Int) Leaf Leaf Leaf)
   in Peel
        (Proxy :: Proxy Z)
        Zipper.Nil
        Zipper.Nil
        (sCns
           (CS (CS CZ))
           (AtSet (Trivial (STreeInt 1) (STreeInt 1)) :*
            AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
            AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
            AtFix
              (Peel
                 (Proxy :: Proxy Z)
                 Zipper.Nil
                 Zipper.Nil
                 (Schg (CS CZ) (CS (CS CZ)) (A0 two three))) :*
            NP0))

-- however, we can be more 'precise' as well
-- we only pinpoint the part that matters, the other leafs are just copied.
-- that is, we're going to change Two to Three, and add a field
p13' :: Almu TreeSingl FamTreeInt CodesTreeInt Z
p13' =
  Peel
    (Proxy :: Proxy Z)
    Zipper.Nil
    Zipper.Nil
    (sCns
       (CS (CS CZ))
       (AtSet (Trivial (STreeInt 1) (STreeInt 1)) :*
        AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
        AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp) :*
        AtFix
          (Peel
             (Proxy :: Proxy Z)
             Zipper.Nil
             Zipper.Nil
             (Schg
                (CS CZ)
                (CS (CS CZ))
                (AX NP0 NP0 (AtSet (Trivial (STreeInt 3) (STreeInt 3))) $
                 AX
                   NP0
                   NP0
                   (AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp)) $
                 AX
                   NP0
                   NP0
                   (AtFix (Peel (Proxy :: Proxy Z) Zipper.Nil Zipper.Nil Scp)) $
                 A0 NP0 (NA_I (deep @FamTreeInt Leaf) :* NP0)))) :*
        NP0))


