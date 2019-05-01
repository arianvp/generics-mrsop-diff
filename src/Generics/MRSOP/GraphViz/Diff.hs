module Generics.MRSOP.GraphViz.Diff where

import Control.Monad
import Control.Monad.State
import Data.Proxy
import Data.Monoid

import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Colors
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.Attributes.HTML
import Data.GraphViz.Types.Monadic hiding (Str)

import Data.Text.Lazy (pack)

import Generics.MRSOP.Base
import Generics.MRSOP.Util
import Generics.MRSOP.Diff
import Generics.MRSOP.GraphViz
import Generics.MRSOP.GraphViz.Deep




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

mkTable i name cells =
  lift $
  node
    i
    [ shape PlainText
    , toLabel $
      HTable
        Nothing
        []
        [Cells (LabelCell [] (Text [Str (pack name)]) : cells)]
    ]




--    +-----+-----+                  +
--    |  -  | +   |            |     |
--    +-----+-----+                  v
visualizeAt :: (Show1 ki, HasDatatypeInfo ki fam codes) => At ki codes x -> DotSM NodeId
visualizeAt  at =
  case at of
    AtSet (Trivial kdel kins) ->
      let table x = HTable Nothing [] [Cells x]
       in freshNode
            [ shape PlainText
            , toLabel . table $
              [ LabelCell
                  [BGColor (toColor Red)]
                  (Text [Str . pack . show1 $ kdel])
              , LabelCell
                  [BGColor (toColor Green)]
                  (Text [Str . pack . show1 $ kins])
              ]
            ]
    AtFix i -> visualizeAlmu i


data VisAl = VisAl
  { source :: [Cell]
  , target :: [Cell]
  }

instance Monoid VisAl where
  mempty = VisAl mempty mempty
  mappend (VisAl s t) (VisAl s' t') = VisAl (mappend s s') (mappend t t')

--    +--------+-----+-----+-----+-----+ 
--    | c1     |  -  |     |     |     |
--    +--------+-----+-----+-----+-----+
--                      |     |     |
--                +-----+     |     |
--                |           |     |
--                v           v     v
--    +--------+-----+-----+-----+-----+-----+
--    | c2     |     |  +  |     |     |  +  |
--    +--------+-----+-----+-----+-----+-----+
--                |     |     |     |     |
--                v     v     v     v     v

visualizeAl' 
  :: (Show1 ki, HasDatatypeInfo ki fam codes) 
  => NodeId 
  -> NodeId 
  -> Al ki codes xs ys 
  -> DotSM VisAl
visualizeAl' source target al =
  case al of
    A0        ->  pure mempty
    AIns x xs ->  do
      aha <- preallocatePortName
      at' <- visualizeNA x
      case at' of
        Konstant k ->  (mempty {target = [ LabelCell [BGColor (toColor Green), Port aha] (Text [Str (pack k)])]} <>)  <$> visualizeAl' source target xs
        Recurse r -> do
          makeEdgePN (target, aha) r
          (mempty {target = [ LabelCell [BGColor (toColor Green), Port aha] (Text [Str (pack " ")])]} <>)  <$> visualizeAl' source target xs

    ADel x xs -> (mempty {source = [ LabelCell [BGColor (toColor Red  )] (Text [Str (pack " ")])]} <>) <$> visualizeAl' source target xs
    AX   x xs -> do
      sp <- preallocatePortName
      tp <- preallocatePortName
      makeEdgePP (source, sp) (target, tp)
      at' <- visualizeAt x
      makeEdgePN (target, tp) at'
      let visal = mempty
                    { source = [LabelCell [Port sp] (Text [Str (pack " ")])]
                    , target = [LabelCell [Port tp] (Text [Str (pack " ")])]
                    }
      (visal <>) <$> visualizeAl' source target xs

visualizeAl 
  :: (Show1 ki, HasDatatypeInfo ki fam codes) 
  => ConstructorName 
  -> ConstructorName 
  -> Al ki codes xs ys 
  -> DotSM NodeId
visualizeAl c1 c2 al = do
  sourceTable <- preallocateNodeId
  targetTable <- preallocateNodeId
  visAl <- visualizeAl' sourceTable targetTable al
  mkTable sourceTable c1 (source visAl)
  mkTable targetTable c2 (target visAl)

  lift $ edge sourceTable targetTable [Style [SItem Invisible []]]
  pure sourceTable

--    +--------+-----+-----+-----+-----+ 
--    | constr |     |     | ... |     |
--    +--------+-----+-----+-----+-----+
--                |     |     |     |
--                v     v     v     v
visualizeAts 
  :: (Show1 ki, HasDatatypeInfo ki fam codes) 
  => ConstructorName 
  -> NP (At ki codes) xs 
  -> DotSM NodeId
visualizeAts c xs = do
  self <- preallocateNodeId
  cells <- elimNPM (mkCell self) xs
  mkTable self c cells
  pure self
  where 
    mkCell self at = do
      port <- preallocatePortName
      at' <- visualizeAt at
      let cell = LabelCell [Port port] (Text [Str (pack " ")])
      makeEdgePN (self, port) at'
      pure cell




visualizeSpine 
  :: (Show1 ki, HasDatatypeInfo ki fam codes) 
  => DatatypeInfo xs 
  -> DatatypeInfo ys 
  -> Spine ki codes xs ys 
  -> DotSM NodeId
visualizeSpine ix iy Scp = freshNode [toLabel "Scp"]
visualizeSpine ix iy (SCns c ats) = visualizeAts (constructorName $ constrInfoLkup c ix) ats
visualizeSpine ix iy (SChg c1 c2 al) = 
  visualizeAl 
    (constructorName $ constrInfoLkup c1 ix)
    (constructorName $ constrInfoLkup c2 iy) 
    al
  

--    +--------+-----+-----+-----+-----+ 
-- -  | constr | p 1 |  *  | ... | p n |
--    +--------+-----+-----+-----+-----+
--                      |
--                      v
npHoleToCellsD
  :: (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes) 
  => ConstructorName
  -> NodeId 
  -> PortName 
  -> DelCtx ki codes ix xs -> DotSM [Cell]
npHoleToCellsD constrName self port h =
  let strLabel p x = LabelCell ( BGColor (toColor Red) : p) (Text [Str (pack x)])
      toCell (Recurse n) = do
              port <- preallocatePortName
              makeEdgePN (self, port) n
              pure $ strLabel [Port port] " "
      toCell (Konstant k) = pure (strLabel [] k)
   in case h of
        H (AlmuMin almu) poa -> do
          fields <- elimNPM visualizeNA poa
          x <- visualizeAlmu almu
          makeEdgePN (self, port) x
          (strLabel [Port port] "*" :) <$> traverse toCell fields
        T na h' -> do
          na' <- visualizeNA na
          na'' <- toCell na' 
          l <- npHoleToCellsD constrName self port h'
          pure (na'' : l)

visualizeDelCtx 
  :: (HasDatatypeInfo ki fam codes, IsNat ix, Show1 ki) 
  => ConstructorName 
  -> DelCtx ki codes ix xs -> DotSM NodeId
visualizeDelCtx c ctx = do
  self <- preallocateNodeId
  port <- preallocatePortName
  cells <- npHoleToCellsD c self port ctx
  table <- mkTable self c cells
  pure self

--    +--------+-----+-----+-----+-----+ 
-- +  | constr | p 1 |  *  | ... | p n |
--    +--------+-----+-----+-----+-----+
--                      |
--                      v
npHoleToCellsI
  :: (Show1 ki, IsNat ix, HasDatatypeInfo ki fam codes) 
  => ConstructorName
  -> NodeId 
  -> PortName 
  -> InsCtx ki codes ix xs -> DotSM [Cell]
npHoleToCellsI constrName self port h =
  let strLabel p x = LabelCell ( BGColor (toColor Green) : p) (Text [Str (pack x)])
      toCell (Recurse n) = do
              port <- preallocatePortName
              makeEdgePN (self, port) n
              pure $ strLabel [Port port] " "
      toCell (Konstant k) = pure (strLabel [] k)
   in case h of
        H almu poa -> do
          fields <- elimNPM visualizeNA poa
          x <- visualizeAlmu almu
          makeEdgePN (self, port) x
          (strLabel [Port port] "*" :) <$> traverse toCell fields
        T na h' -> do
          na' <- visualizeNA na
          na'' <- toCell na' 
          l <- npHoleToCellsI constrName self port h'
          pure (na'' : l)

visualizeInsCtx 
  :: (HasDatatypeInfo ki fam codes, IsNat ix, Show1 ki) 
  => ConstructorName 
  -> InsCtx ki codes ix xs
  -> DotSM NodeId
visualizeInsCtx c ctx = do
  self <- preallocateNodeId
  port <- preallocatePortName
  cells <- npHoleToCellsI c self port ctx
  table <- mkTable self c cells
  pure self

visualizeAlmu 
  :: forall ki fam codes ix iy
   . (Show1 ki, IsNat ix, IsNat iy, HasDatatypeInfo ki fam codes)
  => Almu ki codes ix iy
  -> DotSM NodeId
visualizeAlmu (Spn spn) = 
  visualizeSpine 
    (datatypeInfo (Proxy @fam) (getSNat (Proxy @ix))) 
    (datatypeInfo (Proxy @fam) (getSNat (Proxy @iy)))
    spn 

visualizeAlmu (Ins c ctx) = 
    visualizeInsCtx 
      (constructorName (constrInfoLkup c (datatypeInfo (Proxy @fam) (getSNat (Proxy @iy)))))
      ctx
visualizeAlmu (Del c ctx) =
    visualizeDelCtx 
      (constructorName (constrInfoLkup c (datatypeInfo (Proxy @fam) (getSNat (Proxy @ix)))))
      ctx
