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

gdiff_reflexive :: Tree Int -> Bool
gdiff_reflexive t = 
  let t' = deep @FamTreeInt t
      es = GDiff.getDiff $ GDiff.diff t' t'
  in case GDiff.apply es t' of
      Just t'' ->  t' == t'' 
      Nothing -> False

gdiff_apply_diff :: Tree Int -> Tree Int -> Bool
gdiff_apply_diff t1 t2 =
  let t1' = deep @FamTreeInt t1
      t2' = deep @FamTreeInt t2
      es  = GDiff.getDiff $ GDiff.diff t1' t2'
  in case GDiff.apply es t1' of
        Just t2'' -> t2' == t2''
        Nothing -> False


tests :: IO [Test]
tests = return 
  [ prop gdiff_reflexive , prop gdiff_apply_diff ]
