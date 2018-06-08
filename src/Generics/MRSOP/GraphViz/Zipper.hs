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

module Generics.MRSOP.GraphViz.Zipper where

import Control.Monad
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.Zipper
import qualified Generics.MRSOP.Zipper as Z
import Text.Dot

visualizeCtxs ::
     forall ki fam codes ix iy.
     (IsNat ix , IsNat iy, Show1 ki, HasDatatypeInfo ki fam codes)
  => Ctxs ki fam codes ix iy
  -> Dot NodeId
visualizeCtxs ctxs =
  go ctxs (node [])
  where
    go :: Ctxs ki fam codes ix iy -> Dot NodeId -> Dot NodeId
    go ctxs pointed =
      case ctxs of
        -- does it actually make sense to have an empty zipper at all?
        -- does this actually work?
        Z.Nil -> pointed
        Z.Cons ctx ctxs -> undefined

visualizeLoc ::
     forall ki fam codes ix. (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Loc ki fam codes ix
  -> Dot NodeId
visualizeLoc (Loc (El ty) ctxs) = visualizeCtxs ctxs
