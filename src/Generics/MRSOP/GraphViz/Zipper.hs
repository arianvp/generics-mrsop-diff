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

-- T 1 $ H [2,3]   => |1|*|2|3|
npHoleToCells :: (Show1 ki) => String -> NodeId -> NPHole ki fam ix xs -> [Cell]
npHoleToCells constrName self h =
  let strLabel x = LabelCell [] (Text [Str (pack x)])
      recToCell rec = strLabel " "
      kToCell k = strLabel (show1 k)
   in case h of
        H poa -> strLabel "*" : elimNP (elimNA kToCell recToCell) poa
        T na h' ->
          elimNA kToCell recToCell na : npHoleToCells constrName self h'

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
  => Constr sum n
  -> DatatypeInfo sum
  -> NPHole ki fam ix (Lkup n sum)
  -> DotSM NodeId
npHoleToTable c info h = do
  let constrInfo = constrInfoLkup c info
      constrName = constructorName constrInfo
      dataName = showDatatypeName (datatypeName info)
  self <- preallocateNodeId
  let cells = npHoleToCells constrName self h
      table =
        HTable
          Nothing
          []
            {-Cells
              [ LabelCell
                  [ColSpan (fromIntegral $ length cells)]
                  (Text [Str (pack dataName)])
              ]
          , -}
          [Cells (LabelCell [] (Text [Str (pack constrName)]): cells)]
  lift $ node self [shape PlainText, toLabel table]
  pure self

getCtxsIx :: Ctxs ki fam codes iy ix -> Proxy ix
getCtxsIx _ = Proxy

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
--     | Kek | 1 | * | 1 |   |    <= this NodeId is returned, and its the callers responsibility to draw the arrow from it
--     +-----+---+---+---+---+
-- A forgetful mapping from a stack of contexts to a stack of NodeIds
visualizeCtxs' ::
     forall ki fam sum codes x xs ix iy.
     (Show1 ki, IsNat ix, IsNat iy, HasDatatypeInfo ki fam codes)
  => Ctxs ki fam codes ix iy
  -> DotSM [NodeId]
visualizeCtxs' ctxs =
  case ctxs of
    Z.Nil -> pure []
    Z.Cons (Ctx c h) ctxs' ->
      (:) <$>
      npHoleToTable
        c
        (datatypeInfo (Proxy :: Proxy fam) (getSNat (getCtxsIx ctxs')))
        h <*>
      visualizeCtxs' ctxs'

-- Takes a ctxs, visualizes each ctx. tacks arrows in between,
-- and returns all the node ids
visualizeCtxs ::
     forall ki fam sum codes x xs ix iy.
     (Show1 ki, IsNat ix, IsNat iy, HasDatatypeInfo ki fam codes)
  => Ctxs ki fam codes ix iy
  -> DotSM VisCtxs
visualizeCtxs ctxs = do
  nids <- visualizeCtxs' ctxs
  xs <- zipWithM (\a b -> lift (a --> b) >> pure b) nids (tail nids)
  pure $
    case xs of
      [] -> EmptyCtxs
      [a] -> HeadLast a a
      xs -> HeadLast (head xs) (last xs)

data VisCtxs
  = EmptyCtxs -- ^ The zipper was empty
  | HeadLast NodeId -- ^ The zipper contained at least two elements
             NodeId

visualizeLoc ::
     forall ki fam sum codes x xs ix iy.
     (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Loc ki fam codes ix
  -> DotSM VisCtxs
visualizeLoc (Loc e ctxs) = visualizeCtxs ctxs
