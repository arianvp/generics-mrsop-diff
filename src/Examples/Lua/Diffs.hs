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

module Examples.Lua.Diffs where
import Data.Type.Equality

import Generics.MRSOP.TH
import Generics.MRSOP.Opaque
import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.GDiff
import Language.Lua
import Examples.Lua


quicksort = do
  Right y <- parseFile "./lua/quicksort.lua"
  pure y


quicksort' = fmap (deep @FamStat) quicksort


