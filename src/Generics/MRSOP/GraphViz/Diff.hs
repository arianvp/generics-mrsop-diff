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
import Data.GraphViz.Types.Monadic
import Data.Proxy
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
visualizeAlmu (Peel piy dels inss spine) = do
  dels' <- freshNode [toLabel "TODO: Ctxs"]
  inss' <- freshNode [toLabel "TODO: Ctxs"]
  lift $ dels' --> inss'
  spine' <- visualizeSpine (Proxy :: Proxy ix) spine
  lift $ inss' --> spine'
  pure spine'

--- So sum is not enough, we want
--  (Lkup ix codes)
--
--  but then at the usage site     It iwll complain that
--  cannot solve:   (Lkup ix codes) ~ (Lkup ix0 codes)
visualizeSpine ::
     (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy ix
  -> Spine ki fam codes (Lkup ix codes)
  -> DotSM NodeId
visualizeSpine p spn =
  case spn of
    Scp -> freshNode [toLabel "Scp"] -- lets do a blue one that says copy
    Schg c1 c2 al -> helper p c1 c2 al
      -- visualizeAl _ c1 c2 al
        -- Red Green box with constructor
        --

helper2 ::
     forall ix ki fam codes xs. (IsNat ix, HasDatatypeInfo ki fam codes)
  => At ki fam codes
helper ::
     forall ix ki fam codes n1 n2 p1 p2.
     (IsNat ix, Show1 ki, HasDatatypeInfo ki fam codes)
  => Proxy ix
  -> Constr (Lkup ix codes) n1
  -> Constr (Lkup ix codes) n2
  -> Al ki fam codes p1 p2
  -> DotSM NodeId
helper p c1 c2 al =
  let info = datatypeInfo (Proxy :: Proxy fam) (getSNat p)
      dataName = showDatatypeName (datatypeName info)
      constrInfo1 = constrInfoLkup c1 info
      constrName1 = constructorName constrInfo1
      constrInfo2 = constrInfoLkup c2 info
      constrName2 = constructorName constrInfo2
   in case al of
        A0 poa1 poa2 -> do
          a1 <- preallocateNodeId
          a2 <- preallocateNodeId
          cells1 <- npToCells constrName1 a1 poa1
          cells2 <- npToCells constrName2 a2 poa2
          pure a2
        AX poa1 poa2 at al' -> do
          _ at
          a1 <- preallocateNodeId
          a2 <- preallocateNodeId
          cells1 <- npToCells constrName1 a1 poa1
          cells2 <- npToCells constrName2 a2 poa2
          helper p c1 c2 al'
