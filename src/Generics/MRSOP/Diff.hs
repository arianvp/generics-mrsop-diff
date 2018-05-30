{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module Generics.MRSOP.Diff where

import Generics.MRSOP.Base
import Generics.MRSOP.Base (match)
import Generics.MRSOP.Util

data Almu :: Nat -> * where

data At :: Atom kon -> * where
  Set :: NA at ki fam -> NA at ki fam -> At (K at)
  Fix :: Almu n -> At (I n)

data Al :: [Atom kon] -> [Atom kon] -> * where
  A0 :: Al '[] '[]
  AD :: NA At ki fam -> Al pi1 pi2 -> Al (a ': pi1)  pi2
  AI :: NA At ki fam -> Al pi1 pi2 -> Al pi1         (a ': pi2)
  AX :: At a         -> Al pi1 pi2 -> Al pi1         pi2

data S (sum :: [[Atom kon]]) :: * where
  SCns :: Constr sum n -> NP At (Lkup n sum) -> S sum
  SChg :: Constr sum n1 -> Constr sum n2 -> Al (Lkup n1 sum) (Lkup n2 sum) -> S sum


{-
data S (at :: Atom kon -> *) 
       (al :: [Atom kon] -> [Atom kon] -> *)
       (sum  :: [[Atom kon]]) :: * where
  Scp :: S at al s
  Scns :: Constr sum n 
       -> NP at (Lkup n sum) 
       -> S at al s
  Schg :: Constr sum n1
       -> Constr sum n2
       -- TODO  n1 `neq` ne2
       -> al (Lkup n1 sum) (Lkup n2 sum) -> S at al sum



data Al (at :: Atom kon -> *) :: [Atom kon] -> [Atom kon] -> * where
  A0 :: Al at '[] '[]
  AD :: NA at ki fam -> Al at pi1 pi2 -> Al at (a ': pi1)  pi2
  AI :: NA at ki fam -> Al at pi1 pi2 -> Al at pi1         (a ': pi2)
  AX :: at a         -> Al at pi1 pi2 -> Al at pi1         pi2



data At (patchRec :: Nat -> *) :: Atom kon -> * where
  Set :: NA at ki fam -> NA at ki fam -> At patchRec (K at)
  Fix :: patchRec n -> At patchRec (I n)


-- utility because we can't partially apply types
data Almu1:: Nat -> * where
  Almu1 :: Almu a a -> Almu1 a


{-
  data InsCtx2 (ν₁ : Fin n) : Prod n → Set where
    here  : {ν₂ : Fin n}{π : Prod n} → Alμ ν₁ ν₂ → ⟦ π ⟧P (Fix φ) → InsCtx2 ν₁ (I ν₂ ∷ π)
    there : {α : Atom n}{π : Prod n} → ⟦ α ⟧A (Fix φ) → InsCtx2 ν₁ π → InsCtx2 ν₁ (α ∷ π)
-}
data InsCtx (n1 :: Nat) :: [Atom kon] -> * where
  InsHere ::  Almu n1 n2 -> PoA ki (Fix ki codes) sum -> InsCtx n1 (I n2  ': sum)
  InsThere ::  InsCtx n1 pi

data DelCtx (n1 :: Nat) :: [Atom kon] -> * where
  DelHere ::  Almu n2 n1 -> DelCtx n sum
  DelThere :: DelCtx n sum
  
data Almu :: Nat -> Nat -> * where

  -- spn : ∀{ν} → Patch Alμ↓ (⟦ φ ⟧F ν) → Alμ↓ ν
  Spn :: S (At Almu1) (Al (At Almu1)) sum -> Almu n n

  -- ins : ∀ {ν₁ ν₂} (C : Constr' φ ν₂) → InsCtx ν₁ (typeOf' φ ν₂ C) → Alμ ν₁ ν₂
  Ins :: Constr sum n2 ->  InsCtx n1  (Lkup n2 sum) -> Almu n1 n2

  Del :: Constr sum n1 -> DelCtx n2 (Lkup n1 sum) -> Almu n1 n2

  -}
