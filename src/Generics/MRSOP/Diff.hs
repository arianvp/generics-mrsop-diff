{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module Generics.MRSOP.Diff where

import Generics.MRSOP.Base
import Generics.MRSOP.Base (match)
import Generics.MRSOP.Util

{- Once we fix this thing with generic zippers we can do this one instead
data Almu :: Nat -> * where
  Peel :: {- TODO del and ins zippers  -> S (Lkup j fam) -} Almu i
-}


data InsCtx :: Nat -> [Atom kon] -> * where
  InsHere :: Almu n2 n1 ->  InsCtx n2 (I n1 ': prod)
  InsThere :: NA (Fix ki codes) ki a -> InsCtx n prod -> InsCtx n (a ': prod)

data DelCtx :: Nat -> [Atom kon] -> * where
  DelHere :: Almu n1 n2 ->  DelCtx n2 (I n1 ': prod)
  DelThere :: NA (Fix ki codes) ki a -> DelCtx n prod -> DelCtx n (a ': prod)


data Almu :: Nat -> Nat -> * where
  Spn :: S s -> Almu u u
  Ins :: Constr s v -> InsCtx u (Lkup v s) -> Almu u v
  Del :: Constr s u -> DelCtx v (Lkup u s) -> Almu u v

data At :: Atom kon -> * where
  AtSet :: NA at ki fam -> NA at ki fam -> At (K at)
  AtFix :: Almu n n -> At (I n)

data Al :: [Atom kon] -> [Atom kon] -> * where
  A0 :: Al '[] '[]
  AD :: NA At ki fam -> Al pi1 pi2 -> Al (a ': pi1)  pi2
  AI :: NA At ki fam -> Al pi1 pi2 -> Al pi1         (a ': pi2)
  AX :: At a         -> Al pi1 pi2 -> Al (a ': pi1)  (a ': pi2)

npToAl :: NP At xs -> Al xs xs
npToAl NP0  = A0
npToAl (px :* pxs) = AX px (npToAl pxs)

data S (sum :: [[Atom kon]]) :: * where
  SCpy :: S sum
  SChg :: Constr sum n1 -> Constr sum n2 -> Al (Lkup n1 sum) (Lkup n2 sum) -> S sum


sCns :: Constr sum n -> NP At (Lkup n sum) -> S sum
sCns c x = SChg  c c (npToAl x)

