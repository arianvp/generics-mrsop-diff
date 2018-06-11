{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generics.MRSOP.GraphViz.Zipper where

import Control.Monad
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.GraphViz
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper
import qualified Generics.MRSOP.Zipper as Z

import Control.Monad.State
import Data.GraphViz.Attributes
import Data.GraphViz.Types.Monadic


visualizeNPHole ::
     (Show1 ki) => NPHole ki fam ix xs -> [DotSM NodeId]
visualizeNPHole (H poa) =
  let visualizeK k = freshNode [toLabel (show1 k)]
      visualizeI i = freshNode [toLabel "..."]
   in freshNode [toLabel "*"] : elimNP (elimNA visualizeK visualizeI) poa
visualizeNPHole (T a h) =
  let visualizeK k = freshNode [toLabel (show1 k)]
      visualizeI i = freshNode [toLabel "..."]
   in elimNA visualizeK visualizeI a : visualizeNPHole h

(--->) :: NodeId -> NodeId -> DotSM ()
(--->) a b = lift $ a --> b

-- TODO return the entrypoint and exit point
visualizeCtx ::
     forall ki fam sum codes x xs ix.
     (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Ctx ki fam (Lkup ix codes) ix
  -> DotSM NodeId
visualizeCtx (Ctx c h) =
  let info = datatypeInfo (Proxy :: Proxy fam) (getSNat (Proxy :: Proxy ix))
      constrInfo = constrInfoLkup c info
   in do constr <-
           freshNode
             [ toLabel
                 (constructorName constrInfo ++
                  " :: " ++ showDatatypeName (datatypeName info))
             ]
         fields <- sequence $  visualizeNPHole h
         traverse (constr --->) fields
         pure constr

visualizeCtxs :: Ctxs ki fam codes ix iy -> DotSM NodeId
visualizeCtxs = undefined
{-
visualizeCtxs ::
     forall ki fam codes ix iy.
     (IsNat ix, IsNat iy, Show1 ki, HasDatatypeInfo ki fam codes)
  => Ctxs ki fam codes ix iy
  -> [DotSM NodeId]
visualizeCtxs ctxs =
  case ctxs of
    Z.Nil -> []
    Z.Cons c cs -> visualizeCtx c : visualizeCtxs cs

visualizeLoc ::
     forall ki fam codes ix. (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Loc ki fam codes ix
  -> DotSM NodeId
visualizeLoc (Loc (El ty) ctxs) = do
  nodeIds <- sequence $ visualizeCtxs ctxs
  undefined

-}
