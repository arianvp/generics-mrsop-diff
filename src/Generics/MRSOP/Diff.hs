{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module Generics.MRSOP.Diff where

import Generics.MRSOP.Base
import Generics.MRSOP.Util

data S (at :: Atom kon -> *) 
       (al :: [Atom kon] -> [Atom kon] -> *)
       (sum  :: [[Atom kon]]) :: * where
  Scp :: S at al s
  Scns :: Constr n sum 
       -> NP at (Lkup n sum) 
       -> S at al s
  Schg :: Constr n1 sum
       -> Constr n2 sum
       -- TODO  n1 `neq` ne2
       -> al (Lkup n1 sum) (Lkup n2 sum) -> S at al sum




