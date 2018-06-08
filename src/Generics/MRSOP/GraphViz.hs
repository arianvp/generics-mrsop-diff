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

module Generics.MRSOP.GraphViz where

import Control.Monad
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import qualified Generics.MRSOP.Zipper as Zipper
import Text.Dot

import Generics.MRSOP.Examples.SimpTH

showDatatypeName :: DatatypeName -> String
showDatatypeName (Name str) = str
showDatatypeName (x :@: y) =
  showDatatypeName x ++ "(" ++ showDatatypeName y ++ ")"

visualizeNA ::
     (Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy fam
  -> NA ki (Fix ki codes) a
  -> Dot NodeId
visualizeNA Proxy x =
  case x of
    NA_I i -> visualizeFix i
    NA_K k -> node [("label", show1 k)]

visualizeFix ::
     forall ki fam codes ix. (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Fix ki codes ix
  -> Dot NodeId
visualizeFix (Fix rep) =
  case sop rep of
    Tag c prod ->
      let info = datatypeInfo (Proxy :: Proxy fam) (getSNat (Proxy :: Proxy ix))
          constrInfo = constrInfoLkup c info
       in do constr <-
               node
                 [ ( "label"
                   , constructorName constrInfo ++
                     " :: " ++ showDatatypeName (datatypeName info))
                 ]
             fields <- elimNPM (visualizeNA (Proxy :: Proxy fam)) prod
             traverse (constr .->.) fields
             pure constr

visualizeSpine ::
     forall ki fam codes sum . (Show1 ki, HasDatatypeInfo ki fam codes)
  => Spine ki fam codes sum
  -> Dot NodeId
visualizeSpine spn = case spn of
  Scp -> _ -- lets do a blue one that says copy
  Schg _ _ _-> _ -- Red Green box with constructor

visualizeAlmu ::
     forall ki fam codes ix. (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Almu ki fam codes ix
  -> Dot NodeId
visualizeAlmu (Peel Zipper.Nil Zipper.Nil spn) =
  visualizeSpine spn
visualizeAlmu (Peel _ _ spn) = fail "I don't know yet how to visualize you"
