-- | Forget the types, and annotate using Metadata
-- This intermediate structure is used for visualization
module Generics.MRSOP.Diff.Untyped where

-- flattented representation of datatypes
data Sum = Sum String [Prod]
data Prod = [Atom]
data Atom  = I Sum | K String


newtype Constr = Constr String


data AllAt

data S
  = Scns Constr ProdPatch
  | Schg Constr Constr Al

