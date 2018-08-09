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
import Data.GraphViz.Attributes.Complete (PortName(..))
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Printing
import Data.Text.Lazy (pack, Text)



type NodeId = Int

type DotSM = StateT NodeId (DotM NodeId)

dotToText :: String -> DotSM NodeId -> Text
dotToText fp = renderDot . toDot . digraph (Str (pack fp)) . runDotSM 0

runDotSM :: NodeId -> DotSM a -> DotM NodeId a
runDotSM m i = evalStateT i m

-- | Cause we don't construct Tables in the DotSM monad,
-- we need to preallocate names beforehand
preallocatePortName :: DotSM PortName
preallocatePortName = (PN . pack . show) <$> preallocateNodeId

-- | preallocate a NodeId.  We'd prefer if you use `freshNode` instead
preallocateNodeId :: DotSM NodeId
preallocateNodeId = do
  x <- get
  modify (+ 1)
  pure x

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
