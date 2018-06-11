{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generics.MRSOP.GraphViz.Deep where

import Control.Monad
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.GraphViz

import Control.Monad.State
import Data.GraphViz.Attributes
import Data.GraphViz.Types.Monadic


visualizeNA ::
     (Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy fam
  -> NA ki (Fix ki codes) a
  -> DotSM NodeId
visualizeNA Proxy x =
  case x of
    NA_I i -> visualizeFix i
    NA_K k -> freshNode [toLabel (show1 k)]

visualizeFix ::
     forall ki fam codes ix. (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Fix ki codes ix
  -> DotSM NodeId
visualizeFix (Fix rep) =
  case sop rep of
    Tag c prod ->
      let info = datatypeInfo (Proxy :: Proxy fam) (getSNat (Proxy :: Proxy ix))
          constrInfo = constrInfoLkup c info
       in do constr <-
               freshNode
                 [ toLabel
                     (constructorName constrInfo ++
                      " :: " ++ showDatatypeName (datatypeName info))
                 ]
             fields <- elimNPM (visualizeNA (Proxy :: Proxy fam)) prod
             traverse (lift . (constr -->)) fields
             pure constr
