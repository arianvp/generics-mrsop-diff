{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Generics.MRSOP.GraphViz.Deep where

import Data.Functor.Const
import Control.Monad
import Generics.MRSOP.Base
import Generics.MRSOP.Diff
import Generics.MRSOP.GraphViz
import Generics.MRSOP.Opaque
import Generics.MRSOP.TH
import Generics.MRSOP.Util


import Control.Monad.State
import Data.Proxy
import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Complete
  ( Attribute(TailPort)
  , PortPos(LabelledPort)
  )
import Data.GraphViz.Attributes.HTML
import Data.GraphViz.Types.Monadic hiding (Str)
import Data.Text.Lazy (pack)

{-
 - A piece of data is visualized as follows:
 -
 -                 +--------+-----+-----+-----+-----+ 
 -                 | constr | p 1 | p 2 | ... | p n |
 -                 +--------+-----+-----+-----+-----+
 -                             |     |
 -                             |     |
 -                             |     +--------------------+
 -                             |                          |
 -                             v                          v
 -                +--------+-----+-----+-----+-----+      +--------+-----+-----+-----+-----+ 
 -                | constr | p 1 | p 2 | ... | p n |      | constr | p 1 | p 2 | ... | p n |
 -                +--------+-----+-----+-----+-----+      +--------+-----+-----+-----+-----+
 -}
data AtomDot
  = Recurse NodeId
  | Konstant String

visualizeNA ::
     (Show1 ki, HasDatatypeInfo ki fam codes)
  => NA ki (Fix ki codes) a
  -> DotSM AtomDot
visualizeNA x =
  case x of
    NA_I i -> Recurse <$> visualizeFix i
    NA_K k -> pure . Konstant . show1 $ k

-- will create a table, 
npToTable ::
     (Show1 ki, HasDatatypeInfo ki fam codes)
  => String
  -> String
  -> PoA ki (Fix ki codes) xs
  -> DotSM NodeId
npToTable dataName constrName xs = do
  self <- preallocateNodeId
  cells <- npToCells constrName self xs
  let table =
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

npToCells ::
     (Show1 ki, HasDatatypeInfo ki fam codes)
  => String
  -> NodeId
  -> PoA ki (Fix ki codes) xs
  -> DotSM [Cell]
npToCells constrName self xs = do
  fields <- elimNPM visualizeNA xs
  fields' <- traverse toCell fields
  pure (LabelCell [] (Text [Str (pack constrName)]) : fields')
  where
    toCell :: AtomDot -> DotSM Cell
    toCell (Recurse n) = do
      port <- preallocatePortName
      lift $ edge self n [TailPort (LabelledPort port Nothing)]
      pure . LabelCell [Port port] . Text $ [Str " "]
    toCell (Konstant x) = pure . LabelCell [] . Text $ [Str (pack x)]

visualizeFix ::
     forall ki fam codes ix. (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes)
  => Fix ki codes ix
  -> DotSM NodeId
visualizeFix (Fix rep) =
  case sop rep of
    Tag c prod -> do
      let info = datatypeInfo (Proxy :: Proxy fam) (getSNat (Proxy :: Proxy ix))
          constrInfo = constrInfoLkup c info
          constrName = constructorName constrInfo
          dataName = showDatatypeName (datatypeName info)
      npToTable dataName constrName prod

