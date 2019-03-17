{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}

module Test where

import Distribution.TestSuite
import Test.LeanCheck

import Examples.TwoThreetree

import Data.List

import Generics.MRSOP.Base
import qualified Generics.MRSOP.Diff.Annotate as Annotate
import qualified Generics.MRSOP.Diff.Annotate.Translate as Translate
import qualified Generics.MRSOP.Diff  as STDiff
import qualified Generics.MRSOP.GDiff as GDiff
import Generics.MRSOP.Util

prop':: Testable a => a -> TestInstance
prop' y =
        TestInstance
          { run =
              do checkFor 1000 y
                 pure (Finished Pass)
          , name = "succeeds"
          , tags = []
          , options = []
          , setOption = \_ _ -> Right undefined
          }
   
prop :: Testable a => a -> Test
prop = Test . prop'

deriveListable ''Tree

-- TODO: We need to be explicit about in which family it resides. Can we fix that?
gdiff_reflexive :: Tree Int -> Bool
gdiff_reflexive t =
  any (== t) $ GDiff.apply (GDiff.diff @FamTreeInt t t) t

gdiff_apply_diff :: Tree Int -> Tree Int -> Bool
gdiff_apply_diff t1 t2 =
  any (== t2) $ GDiff.apply (GDiff.diff @FamTreeInt t1 t2) t1

--  
gdiff_to_stdiff_transformation_is_sound :: Tree Int -> Tree Int -> Bool
gdiff_to_stdiff_transformation_is_sound t1 t2 =
  let t1' = deep @FamTreeInt t1
      t2' = deep @FamTreeInt t2
      es = GDiff.diff' t1' t2'
      t1'' = Annotate.annSrc t1' es
      t2'' = Annotate.annDest t2' es
      diff =
        Translate.diffAlmu
          (Translate.countCopies t1'')
          (Translate.countCopies t2'')
   in any (== t2') $ STDiff.applyAlmu diff t1'

-- counter example that leancheck gave
regression :: (Tree Int, Tree Int)
regression = (Two 0 Leaf Leaf, Two 0 (Two 0 Leaf Leaf) Leaf)

regression2 :: (Tree Int, Tree Int)
regression2 = (Two 0 (Two 0 Leaf Leaf) Leaf, Two 0 Leaf Leaf)

(lhs, rhs) = regression

-- all the steps, such that we can introspect
lhs' = deep @FamTreeInt lhs
rhs' = deep @FamTreeInt rhs
es  = GDiff.diff' lhs' rhs'
lhs'' = Annotate.annSrc lhs' es
lhs''' = Translate.countCopies $ lhs''
rhs'' = Annotate.annDest rhs' es
rhs''' = Translate.countCopies $ rhs''
diff = Translate.diffAlmu lhs''' rhs'''




tests :: IO [Test]
tests =
  return
    [ prop gdiff_reflexive
    , prop gdiff_apply_diff
    , prop gdiff_to_stdiff_transformation_is_sound
    , prop $ uncurry gdiff_to_stdiff_transformation_is_sound regression
    , prop $ uncurry gdiff_to_stdiff_transformation_is_sound regression2
    ]
