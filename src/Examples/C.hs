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

module Examples.C where
import Language.C.Syntax.AST
import Language.C.Data

import Data.Text (Text)
import Data.Type.Equality

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.GDiff

data CKon = CText | CInt
data CSingl (kon :: CKon) :: * where
  SCText :: String -> CSingl CText
  SCInt :: Int -> CSingl CInt

deriving instance Show (CSingl k)
deriving instance Eq (CSingl k)
instance Show1 CSingl where show1 = show
instance Eq1 CSingl where eq1 = (==)

instance TestEquality CSingl where
  testEquality (SCText _) (SCText _) = Just Refl

-- deriveFamilyWith ''CSingl [t| CTranslationUnit () |]
