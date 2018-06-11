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
     (IsNat ix, Show1 ki, sum ~ Lkup ix codes, prod ~ Lkup n sum)
  => Constr sum n
  -> NPHole ki fam ix prod
  -> [DotSM NodeId]
visualizeNPHole c (H poa) =
  freshNode [toLabel "*"] :
  elimNP (elimNA (\k -> freshNode [toLabel (show k)]) undefined) poa
visualizeNPHole c (T a h) =
  let elimK k = freshNode [toLabel (show k)]
      -- we don't visualize recursion for now, clutters tree
      elimI i =  freshNode [toLabel "..."]
  in
    elimNA elimK elimI  a : visualizeNPHole c h

(--->) :: NodeId -> NodeId -> DotSM ()
(--->) a b = lift $ a --> b

-- TODO should both return the entrypoint and the hole
visualizeCtx ::
     forall ki fam sum codes x xs ix.
     (Show1 ki, IsNat ix, sum ~ Lkup ix codes, HasDatatypeInfo ki fam codes)
  => Ctx ki fam sum ix
  -> DotSM NodeId
visualizeCtx (Ctx c h) =
  let info = datatypeInfo (Proxy :: Proxy fam) (getSNat (Proxy :: Proxy ix))
      constrInfo = constrInfoLkup c info
   -- TODO there is still a bug here, we recreate constr for each step of
   -- recursion, whilst we should only create it once
   in do constr <-
           freshNode
             [ toLabel
                 (constructorName constrInfo ++
                  " :: " ++ showDatatypeName (datatypeName info))
             ]
         fields <- sequence $ visualizeNPHole c h
         traverse (constr --->) fields
         pure constr

    

visualizeCtxs ::
     forall ki fam codes ix iy.
     (IsNat ix , IsNat iy, Show1 ki, HasDatatypeInfo ki fam codes)
  => Ctxs ki fam codes ix iy
  -> [DotSM NodeId]
visualizeCtxs ctxs =
  case ctxs of
    Z.Nil -> []
    Z.Cons c cs -> 
      [freshNode [toLabel "TODO: visualize contexts"]]
      -- visualizeCtx c : visualizeCtxs cs

visualizeLoc ::
     forall ki fam codes ix. (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Loc ki fam codes ix
  -> DotSM NodeId
visualizeLoc (Loc (El ty) ctxs) = do
  nodeIds <- sequence $ visualizeCtxs ctxs
  undefined
