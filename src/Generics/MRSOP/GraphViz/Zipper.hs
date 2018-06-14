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
import Data.GraphViz.Attributes.Complete
  ( Attribute(TailPort)
  , PortPos(LabelledPort)
  )
import Data.GraphViz.Attributes.HTML
import Data.GraphViz.Types.Monadic hiding (Str)
import Data.Proxy
import Data.Text.Lazy (pack)

npHoleToCells :: (Show1 ki) => String -> NodeId -> NPHole ki fam ix xs -> [Cell]
npHoleToCells constrName self h = do
  let recToCell rec = LabelCell [] (Text [Str (pack "...")])
      kToCell k = LabelCell [] (Text [Str (pack (show1 k))])
  case h of
    H poa -> elimNP (elimNA kToCell recToCell) poa
    T na h' -> npHoleToCells constrName self h'

npHoleToTable ::
     (Show1 ki) =>
     Constr sum n -> (Constr sum n -> String) -> NPHole ki fam ix (Lkup n sum) -> DotSM NodeId
npHoleToTable c h = undefined
  {-
  self <- preallocateNodeId
  let cells = npHoleToCells constrName self h
      table =
        HTable
          Nothing
          []
          [ Cells
              [ LabelCell
                  [ColSpan (fromIntegral $ length cells)]
                  (Text [Str (pack dataName)])
              ]
          , Cells cells
          ]
  lift $ node self [shape PlainText, toLabel table]
  pure self
  -}



visualizeCtxs ::
     forall ki fam sum codes x xs ix iy.
     (Show1 ki, IsNat ix,  IsNat iy, HasDatatypeInfo ki fam codes)
  => Proxy ix
  -> Proxy iy
  -> NodeId
  -> Ctxs ki fam codes ix iy
  -> DotSM NodeId
visualizeCtxs px py from ctxs =
  case ctxs of
    Z.Nil -> pure from
    Z.Cons (Ctx c h) ctxs' -> do
      undefined
      -- _ px py ctxs'
      -- visualizeCtxs px py undefined ctxs'
      {-
      npHoleToTable c _ h
      visualizeCtxs from ctxs'
      -}
      {-let info = datatypeInfo (Proxy :: Proxy fam) (getSNat (Proxy :: Proxy ix))
          constrInfo = constrInfoLkup c info
          constrName = constructorName constrInfo
          dataName = showDatatypeName (datatypeName info)
      t <- npHoleToTable dataName constrName h
      lift $ from --> t
      visualizeCtxs t ctxs'-}

