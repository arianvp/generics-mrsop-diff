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
    (EmptyCtxs, EmptyCtxs) -> pure 0
    (EmptyCtxs, HeadLast ih il) -> do
      makeEdgeNP spine' ih 
      -- TODO we might wanna return a portId here
      -- so that we can actually point to the zipper nicely
      pure (fst ih)
    (HeadLast dh dl, EmptyCtxs) -> do
      makeEdgeNP spine' dh
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
    AtSet k -> freshNode [toLabel "K"]
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
          { source =
              elimNP
                (const
                   (LabelCell [BGColor (toColor Green)] (Text [Str (pack " ")])))
                inss <>
              elimNP
                (const
                   (LabelCell [BGColor (toColor Red)] (Text [Str (pack " ")])))
                dels
          }
    AX inss dels at al' -> do
      s <- preallocatePortName
      d <- preallocatePortName
      v <- visualizeAl' p sourceTable targetTable al'
      lift $
        edge
          sourceTable
          targetTable
          [HeadPort (LabelledPort s Nothing), TailPort (LabelledPort d Nothing)]
      pure $ mempty {source = [] , target = [] } <> v

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
  undefined
      -- To recurse, we need to know the previous cell
      -- we're gonna make two tables
      -- After each cell, one can decide to do a certain amount of insertions or deletions
   {-case al of
           A0 poa1 poa2 -> do
             a1 <- preallocateNodeId
             a2 <- preallocateNodeId
             cells1 <- npToCells constrName1 a1 poa1
             cells2 <- npToCells constrName2 a2 poa2
             pure a2
           AX poa1 poa2 at al' -> do
             visualizeAt (Proxy :: Proxy ix) at
             a1 <- preallocateNodeId
             a2 <- preallocateNodeId
             cells1 <- npToCells constrName1 a1 poa1
             cells2 <- npToCells constrName2 a2 poa2
             visualizeAl p c1 c2 al'-}
