module Generics.MRSOP.GraphViz where

import Control.Monad
import Data.Proxy
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util

import Control.Monad.State
import Data.GraphViz.Attributes
import Data.GraphViz.Types.Monadic

type NodeId = Int

type DotSM = StateT NodeId (DotM NodeId)

-- | generates a fresh node. So that we don't need to keep track of names
freshNode :: Attributes -> DotSM NodeId
freshNode a = do
  x <- get
  modify (+ 1)
  lift $ node x a
  pure x

-- | TODO make something nicer, maybe a table
showDatatypeName :: DatatypeName -> String
showDatatypeName (Name str) = str
showDatatypeName (x :@: y) =
  showDatatypeName x ++ "(" ++ showDatatypeName y ++ ")"
