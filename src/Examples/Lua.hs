{-# LANGUAGE TemplateHaskell #-}
module Examples.Lua where
import Language.Lua.Syntax

import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.GDiff

deriveFamily [t| Stat |]
