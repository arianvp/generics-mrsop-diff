{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generics.MRSOP.GraphViz.Diff2 where


import Control.Monad
import Control.Monad.State
import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Colors
import Data.GraphViz.Attributes.Complete
  ( Attribute(HeadPort, TailPort)
  , PortPos(LabelledPort)
  )
import Data.GraphViz.Attributes.HTML
import Data.GraphViz.Types.Monadic hiding (Str)
import Data.Monoid
import Data.Proxy
import Data.Text.Lazy (pack)
import Debug.Trace
import Generics.MRSOP.Base
import Generics.MRSOP.Diff2
import Generics.MRSOP.GraphViz
import Generics.MRSOP.GraphViz.Deep
import Generics.MRSOP.GraphViz.Zipper
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper


visualizeAlmu ::
     forall ix ki fam codes. (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Almu ki codes ix
  -> DotSM NodeId
visualizeAlmu almu = 
  case almu of
    Spn spn -> undefined
    Ins c ctx -> undefined
    Del c ctx -> undefined
    


