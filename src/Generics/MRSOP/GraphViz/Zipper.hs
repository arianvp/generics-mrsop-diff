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
{-# LANGUAGE RankNTypes #-}

module Generics.MRSOP.GraphViz.Zipper where

import Control.Monad
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.GraphViz
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper.Deep
import qualified Generics.MRSOP.Zipper.Deep as Z

import Control.Monad.State
import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Complete
  ( Attribute(HeadPort, TailPort)
  , PortName
  , PortPos(LabelledPort)
  , toColor
  )
import Data.GraphViz.Attributes.HTML
import Data.GraphViz.Types.Monadic hiding (Str)
import Data.Proxy
import Data.Text.Lazy (pack)

-- T 1 $ H [2,3]   => |1|*|2|3|
npHoleToCells ::
     (Show1 ki) => String -> NodeId -> PortName -> NPHole ki codes ix xs -> [Cell]
npHoleToCells constrName self port h =
  let strLabel p x = LabelCell p (Text [Str (pack x)])
      recToCell rec = strLabel [] " "
      kToCell k = strLabel [] (show1 k)
   in case h of
        H poa ->
          strLabel [Port port] "*" : elimNP (elimNA kToCell recToCell) poa
        T na h' ->
          elimNA kToCell recToCell na : npHoleToCells constrName self port h'

--  
--  data Foo = Lol Int Int Int Foo
--
--  Lol 1 2 * (Lol ... )  =>
-- 
--  We dont visualize recursive positions, as we
--  re only interested in the path through products
--
--   TODO decide how we visualize the type of this thing nicely     
--     +-----+---+---+---+---+
--     | Lol | 1 | 2 | * |   |
--     +-----+---+---+---+---+
-- 
--
-- A forgetful mapping from Ctx to NodeId
npHoleToTable ::
     (Show1 ki)
  => X11Color
  -> Constr sum n
  -> DatatypeInfo sum
  -> NPHole ki codes ix (Lkup n sum)
  -> DotSM (NodeId, PortName)
npHoleToTable color c info h = do
  let constrInfo = constrInfoLkup c info
      constrName = constructorName constrInfo
      dataName = showDatatypeName (datatypeName info)
  self <- preallocateNodeId
  port <- preallocatePortName
  let cells = npHoleToCells constrName self port h
      table =
        HTable
          Nothing
          [BGColor (toColor color)]
            {-Cells
              [ LabelCell
                  [ColSpan (fromIntegral $ length cells)]
                  (Text [Str (pack dataName)])
              ]
          , -}
          [Cells (LabelCell [] (Text [Str (pack constrName)]) : cells)]
  lift $ node self [shape PlainText, toLabel table]
  pure (self, port)


-- A stack of Ctxs
--              
--              
--             
--            
-- +-----+---+---+---+---+
-- | Lol | 1 | 2 | * |   |
-- +-----+---+---+---+---+
--                 |
--                 v
--     +-----+---+---+---+---+
--     | Kek | 1 | * | 1 |   |  
--     +-----+---+---+---+---+
-- A forgetful mapping from a stack of contexts to a stack of NodeIds
visualizeCtxs' ::
     forall ki fam sum codes x xs ix iy.
     (Show1 ki, IsNat ix, IsNat iy, HasDatatypeInfo ki fam codes)
  => X11Color
  -> Ctxs ki codes ix iy
  -> DotSM [(NodeId, PortName)]
visualizeCtxs' color ctxs =
  case ctxs of
    Z.Nil -> pure []
    Z.Cons (Ctx c h) ctxs' ->
      (:) <$>
      npHoleToTable
        color
        c
        (datatypeInfo (Proxy :: Proxy fam) (getSNat (getCtxsIx ctxs')))
        h <*>
      visualizeCtxs' color ctxs'

-- Takes a ctxs, visualizes each ctx. tacks arrows in between,
-- and returns all the node ids
visualizeCtxs ::
     forall ki fam sum codes x xs ix iy.
     (Show1 ki, IsNat ix, IsNat iy, HasDatatypeInfo ki fam codes)
  => X11Color
  -> Ctxs ki codes ix iy
  -> DotSM VisCtxs
visualizeCtxs c ctxs = do
  nids <- visualizeCtxs' c ctxs
  xs <- zipWithM (\a b -> makeEdgePP a b >> pure b) nids (tail nids)
  pure $
    case xs of
      [] -> EmptyCtxs
      [a] -> HeadLast a a
      xs -> HeadLast (head xs) (last xs)

-- helpers for edges
-- TODO: move them to other module?
makeEdgePN (n1, p1) n2 =
  lift $ edge n1 n2 [TailPort (LabelledPort p1 Nothing)]

makeEdgeNP n1 (n2, p2) =
  lift $ edge n1 n2 [HeadPort (LabelledPort p2 Nothing)]

makeEdgePP (n1, p1) (n2, p2) =
  lift $
  edge
    n1
    n2
    [TailPort (LabelledPort p1 Nothing), HeadPort (LabelledPort p2 Nothing)]

data VisCtxs
  = EmptyCtxs 
  | HeadLast (NodeId, PortName) 
             (NodeId, PortName)

