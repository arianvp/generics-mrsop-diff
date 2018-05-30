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

module Examples.Expr where
import Data.Type.Equality

import Generics.MRSOP.TH
import Generics.MRSOP.Opaque
import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.GDiff

data Op
  = Mul | Sub | Add
  deriving Show

data Expr
  = Val Int
  | Let String Expr Expr
  | Lam String Expr
  | Op Op Expr Expr
  deriving Show


data EKon = EKInt | EKString

data ESingl (kon :: EKon) :: * where
  ESInt :: Int -> ESingl EKInt
  ESString :: String -> ESingl EKString

deriving instance Show (ESingl k)
deriving instance Eq (ESingl k)

instance Show1 ESingl where
  show1 = show
instance Eq1 ESingl where
  eq1 = (==)
 
instance TestEquality ESingl where
  testEquality (ESInt x) (ESInt y) = Just Refl
  testEquality (ESString x) (ESString y) = Just Refl
  testEquality _ _ = Nothing


deriveFamilyWith ''ESingl [t| Expr |]


e1 , e2 :: Expr
e1 = Val 3
e2 = Op Add (Val 3) (Val 4)


e1' = deep @FamExpr e1
e2' = deep @FamExpr e2

est = diff e1' e2'
es = getDiff est

e2'' = applyES es (NA_I e1' :* NP0)




