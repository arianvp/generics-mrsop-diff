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
import qualified Generics.MRSOP.GDiff as GDiff
import Generics.MRSOP.Util

prop :: Testable a => a ->  Test
prop y =
    let x = TestInstance
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

-- not sure why I need this
instance Eq  (Fix TreeSingl CodesTreeInt 'Z) where
  (==) = eqFix eq1


-- TODO: We need to be explicit about in which family it resides. Can we fix that?
gdiff_reflexive :: Tree Int -> Bool
gdiff_reflexive t =
  case GDiff.apply (GDiff.diff @FamTreeInt t t) t of
    Just t' -> t == t'
    Nothing -> False

gdiff_apply_diff :: Tree Int -> Tree Int -> Bool
gdiff_apply_diff t1 t2 =
  case GDiff.apply (GDiff.diff @FamTreeInt t1 t2) t1 of
    Just t2' -> t2' == t2
    Nothing -> False


--  
gdiff_to_stdiff_transformation_is_sound :: Bool
gdiff_to_stdiff_transformation_is_sound = False


tests :: IO [Test]
tests =
  return
    [ prop gdiff_reflexive
    , prop gdiff_apply_diff
    , prop gdiff_to_stdiff_transformation_is_sound
    ]
