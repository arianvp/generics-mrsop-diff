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

module Generics.MRSOP.GraphViz.Diff where

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
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.GraphViz
import Generics.MRSOP.GraphViz.Deep
import Generics.MRSOP.GraphViz.Zipper
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper

visualizeAlmu ::
     forall ix ki fam codes. (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Almu ki fam codes ix
  -> DotSM NodeId
visualizeAlmu (Peel dels inss spine) = do
  dels' <- visualizeCtxs dels
  inss' <- visualizeCtxs inss
  spine' <- visualizeSpine (Proxy :: Proxy ix) spine
  case (dels', inss') of
    -- Easy case
    (EmptyCtxs, EmptyCtxs) -> pure spine'
    (EmptyCtxs, HeadLast ih il) -> do
      -- Edge from il to spine'
      makeEdgePN il spine'
      -- TODO we might wanna return a portId here
      -- so that we can actually point to the zipper nicely
      pure (fst ih)
    (HeadLast dh dl, EmptyCtxs) -> do
      makeEdgePN dl spine'
      pure (fst dh)
    (HeadLast dh dl, HeadLast ih il) -> do
      makeEdgePP dl ih
      makeEdgePN il spine'
      pure (fst dh)

visualizeSpine ::
     (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy ix
  -> Spine ki fam codes (Lkup ix codes)
  -> DotSM NodeId
visualizeSpine p spn =
  case spn of
    Scp -> freshNode [toLabel "Scp"]
    Schg c1 c2 al -> do
      visualizeAl p c1 c2 al

visualizeAt ::
     forall ix ki fam codes a.
     (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy ix
  -> At ki fam codes a
  -> DotSM NodeId
visualizeAt p at =
  case at of
    AtSet k -> freshNode [toLabel "K->K"]
    AtFix i -> visualizeAlmu i

-- Some state that we keep track off for visualization
data VisAl = VisAl
  { source :: [Cell]
  , target :: [Cell]
  }

instance Monoid VisAl where
  mempty = VisAl mempty mempty
  mappend (VisAl s t) (VisAl s' t') = VisAl (mappend s s') (mappend t t')

visualizeAl' ::
     forall ix ki fam codes n1 n2 p1 p2.
     (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy ix
  -> NodeId
  -> NodeId
  -> Al ki fam codes p1 p2
  -> DotSM VisAl
visualizeAl' p sourceTable targetTable al =
  case al of
    A0 inss dels -> do
      pure $
        mempty
          { source
              -- TODO do insertion here
              -- by doing an elimNPM and calling visualizeDeep 
             =
              elimNP
                (const
                   (LabelCell [BGColor (toColor Green)] (Text [Str (pack " ")])))
                inss <>
              -- NOTE: we ignore deletions
              elimNP
                (const
                   (LabelCell [BGColor (toColor Red)] (Text [Str (pack " ")])))
                dels
          }
    AX inss dels at al'
        -- TODO:
        --  * forntPart: add inss and dels  to tail of list like A0 case
        --  * recursively visualize at
        --  * add two cells, with arrow inbetween
        --  * draw arrow from last cell to visualizaiton of at
        --  * continue recursively on the tail.
        --  * concatenate the results
     -> do
      let frontPart =
            mempty
              { source
                  -- TODO do insertion here
                  -- by doing an elimNPM and calling visualizeDeep 
                 =
                  elimNP
                    (const
                       (LabelCell
                          [BGColor (toColor Green)]
                          (Text [Str (pack " ")])))
                    inss <>
                  -- NOTE: we ignore deletions
                  elimNP
                    (const
                       (LabelCell
                          [BGColor (toColor Red)]
                          (Text [Str (pack " ")])))
                    dels
              }
      s <- preallocatePortName
      d <- preallocatePortName
      let midPart =
            mempty
              { source =
                  elimNP
                    (const
                       (LabelCell
                          [Port s, BGColor (toColor Green)]
                          (Text [Str (pack " ")])))
                    inss <>
                  elimNP
                    (const
                       (LabelCell
                          [Port d , BGColor (toColor Red)]
                          (Text [Str (pack " ")])))
                    dels
              }
      lift $
        edge
          sourceTable
          targetTable
          [HeadPort (LabelledPort s Nothing), TailPort (LabelledPort d Nothing)]
      at' <- visualizeAt p at
      lift $ edge targetTable at' [HeadPort (LabelledPort d Nothing)]
      tail <- visualizeAl' p sourceTable targetTable al'
      pure $ frontPart <> midPart <> tail

visualizeAl ::
     forall ix ki fam codes n1 n2 p1 p2.
     (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy ix
  -> Constr (Lkup ix codes) n1
  -> Constr (Lkup ix codes) n2
  -> Al ki fam codes p1 p2
  -> DotSM NodeId
visualizeAl p c1 c2 al = do
  let info = datatypeInfo (Proxy :: Proxy fam) (getSNat p)
      dataName = showDatatypeName (datatypeName info)
      constrInfo1 = constrInfoLkup c1 info
      constrName1 = constructorName constrInfo1
      constrInfo2 = constrInfoLkup c2 info
      constrName2 = constructorName constrInfo2
      mkTable i cells =
        lift $
        node i [shape PlainText, toLabel $ HTable Nothing [] [Cells cells]]
  sourceTable <- preallocateNodeId
  destTable <- preallocateNodeId
  visAl <- visualizeAl' p sourceTable destTable al
  mkTable sourceTable (source visAl)
  mkTable destTable (target visAl)
  pure sourceTable
