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
import qualified Generics.MRSOP.Diff2 as STDiff
import qualified Generics.MRSOP.GDiff as GDiff
import Generics.MRSOP.Util

prop :: Testable a => a -> Test
prop y =
  let x =
        TestInstance
          { run =
              do checkFor 1000 y
                 pure (Finished Pass)
          , name = "succeeds"
          , tags = []
          , options = []
          , setOption = \_ _ -> Right undefined
          }
   in Test x

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

tests :: IO [Test]
tests =
  return
    [ prop gdiff_reflexive
    , prop gdiff_apply_diff
    , prop gdiff_to_stdiff_transformation_is_sound
    ]
