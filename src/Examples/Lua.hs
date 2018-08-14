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

module Examples.Lua where
import Language.Lua.Syntax

import Data.Text (Text)
import Data.Type.Equality

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util

data LuaKon = LuaText
data LuaSingl (kon :: LuaKon) :: * where
  SLuaText :: Text -> LuaSingl LuaText

deriving instance Show (LuaSingl k)
deriving instance Eq (LuaSingl k)
instance Show1 LuaSingl where show1 = show
instance Eq1 LuaSingl where eq1 = (==)

instance TestEquality LuaSingl where
  testEquality (SLuaText _) (SLuaText _) = Just Refl

deriveFamilyWith ''LuaSingl [t| Block |]
