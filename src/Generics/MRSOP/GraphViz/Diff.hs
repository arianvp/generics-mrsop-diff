module Generics.MRSOP.GraphViz.Diff where

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
