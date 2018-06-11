{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Generics.MRSOP.GraphViz.Diff where

import Control.Monad
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.GraphViz
import Generics.MRSOP.GraphViz.Zipper
import Control.Monad.State
import Data.GraphViz.Attributes
import Data.GraphViz.Types.Monadic

visualizeAlmu ::
     forall ki fam codes ix. (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Almu ki fam codes ix
  -> DotSM NodeId
visualizeAlmu (Peel dels inss spine) = do
  undefined


{-
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
visualizeAlmu (Peel _ _ spn) = fail "I don't know yet how to visualize you"-}
