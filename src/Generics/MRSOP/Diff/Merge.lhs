\begin{code}
{-# OPTIONS_GHC -Wall -Wno-unused-matches -Wno-name-shadowing #-}
module Generics.MRSOP.Diff.Merge where

import Data.Proxy
import Data.Type.Equality
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Diff2


data Merged (ki :: kon -> *) (codes :: [[[Atom kon]]]) (ix :: Nat) :: * where
  Merged :: Almu ki codes ix iy -> Merged ki codes ix

-- assumes that this alignment is simply an NP
-- should return a descriptive error message in the future
-- for debugging purposes
assumeNP :: Al ki codes xs xs -> Maybe (NP (At ki codes) xs)
assumeNP (A0 NP0 NP0) = Just NP0
assumeNP (A0 _ _) = Nothing
assumeNP (AX NP0 (_ :* _) _ _) = Nothing
assumeNP (AX (_ :* _) _ _ _) = Nothing
assumeNP (AX NP0 NP0 px xs) = (px :*) <$> assumeNP xs


makeIdAt :: NA ki (Fix ki codes) a -> At ki codes a
makeIdAt (NA_I _) = AtFix (Spn Scp)
makeIdAt (NA_K k) = AtSet (Trivial k k)

{-mergeAtCtx
  :: NP (At ki codes) xs
  -> Ctx ki codes (Almu ki codes) ix xs
  -> Maybe (Ctx ki codes (Almu ki codes) ix xs)
mergeAtCtx (AtFix a :* as) (H almu rest) =
  -- TODO: This is _very_ nasty 
  -- xs ~  'I 
  H <$> _ a almu <*> pure rest
  -- H <$> mergeAlmu a almu <*> pure rest
mergeAtCtx (AtFix a :* as) (T a' ctx) = T a' <$> mergeAtCtx as ctx
mergeAtCtx (AtSet a :* as) (T a' ctx) = T a' <$> mergeAtCtx as ctx

mergeCtxAt 
  :: Ctx ki codes (Almu ki codes) ix xs
  -> NP (At ki codes) xs
  -> Maybe (Almu ki codes ix ix)
mergeCtxAt (H almu rest) (AtFix a :* as) = mergeAlmu almu a
mergeCtxAt (T a' ctx) (AtFix a :* as) = mergeCtxAt ctx as
mergeCtxAt (T a' ctx) (AtSet a :* as) = mergeCtxAt ctx as
-}

getTarget :: forall ki codes ix iy. (IsNat iy) => Almu ki codes ix iy -> SNat iy
getTarget = sNatFixIdx

getSource :: forall ki codes ix iy. (IsNat ix) => Almu ki codes ix iy -> SNat ix
getSource _ = getSNat (Proxy :: Proxy ix)

-- TODO: Very Skeptical about this approach
{-mergeCtxAlmu
  :: (IsNat ix, IsNat iy)
  => Constr (Lkup ix codes) c
  -> InsCtx ki codes ix (Lkup c (Lkup ix codes))
  -> Almu ki codes ix iy
  -> Maybe (NP (At ki codes) (Lkup c (Lkup ix codes)))
mergeCtxAlmu c (H almu' xs) almu =
  case testEquality (getSource almu) (getTarget almu') of
    Just Refl -> do
      x <- mergeAlmu almu almu'
      let xs' = mapNP makeIdAt xs
      pure $ AtFix x :* xs'
    Nothing -> Nothing
mergeCtxAlmu c (T a ctx) almu = do
  let a' =  makeIdAt a 
  xs' <- mergeCtxAlmu  ctx almu 
  pure $ a' :* xs'

mergeAlmuCtx
  :: (IsNat ix, IsNat iy)
  => Almu ki codes ix iy
  -> InsCtx ki codes ix xs
  -> Maybe (InsCtx ki codes ix xs)
mergeAlmuCtx almu (H almu' rest) =
  case testEquality (sNatFixIdx almu) (sNatFixIdx almu') of
    Just Refl -> do
      almu'' <- mergeAlmu almu almu'
      pure $ H almu'' rest
    Nothing -> Nothing
mergeAlmuCtx almu (T a ctx) = T a <$> mergeAlmuCtx almu ctx
-}

mergeAlAt
  :: AlOld ki codes xs ys 
  -> NP (At ki codes) xs
  -> Maybe (NP (At ki codes) ys)
mergeAlAt OA0 NP0 =  Just NP0
mergeAlAt (OAIns at al) NP0 = (:*) <$> pure (makeIdAt at) <*> mergeAlAt al NP0
mergeAlAt (OAIns at al) (a :* as) = (:*) <$> pure (makeIdAt at) <*> mergeAlAt al (a :* as)
mergeAlAt (OADel at al) (a :* as) = mergeAlAt al as
mergeAlAt (OAX at al) (a :* as) = (:*) <$> mergeAt at a <*> mergeAlAt al as

mergeAtAl
  :: NP (At ki codes) xs
  -> AlOld ki codes xs ys
  -> Maybe (AlOld ki codes xs ys)
mergeAtAl at al =
  case (at, al) of
    (NP0, OA0) -> Just OA0
    (NP0, OAIns at' al') -> Just $ OAIns at' al'
    (a :* as, OAIns at' al') -> OAIns at' <$> mergeAtAl (a :* as) al'
    (a :* as, OADel at' al') -> OADel at' <$> mergeAtAl as al'
    (a :* as, OAX at' al') -> OAX <$> mergeAt a at' <*> mergeAtAl as al'

mergeAt :: At ki codes a -> At ki codes a -> Maybe (At ki codes a)
mergeAt (AtSet _) (AtSet k2) =
  -- TODO TODO TODO TODO
  -- if disjoint  then k2
  -- else Nothing
  Just (AtSet k2)
mergeAt (AtFix almu1) (AtFix almu2) = do
  let x = sNatFixIdx almu1 
  let y = sNatFixIdx almu2
  case testEquality x y of
    Just Refl -> do
      almu <- mergeAlmu almu1 almu2
      pure $ AtFix almu
    Nothing -> Nothing

mergeAts
  :: NP (At ki codes) xs 
  -> NP (At ki codes) xs 
  -> Maybe (NP (At ki codes) xs)
mergeAts NP0 NP0 = Just NP0
mergeAts (px :* xs) (py :* ys) = (:*) <$> mergeAt px py <*> mergeAts xs ys


mergeSpine
  :: Spine ki codes xs
  -> Spine ki codes xs 
  -> Maybe (Spine ki codes xs)
mergeSpine Scp s = pure s
mergeSpine s Scp = pure s
mergeSpine (Schg c1 c2 al1) (Schg c3 c4 al2) =
  -- sCns sCns
  case (testEquality c1 c2, testEquality c3 c4) of
    (Just Refl, Just Refl) ->
      case testEquality c1 c3 of
        Just Refl -> do
          ats1 <- assumeNP al1
          ats2 <- assumeNP al2
          sCns c1 <$> mergeAts ats1 ats2
        Nothing -> Nothing
    -- sCns   sChg
    --
    -- sChg c1 c1    sChg c2 c3
    -- 
    (Just Refl, Nothing) -> do
      case testEquality c1 c3 of
        Just Refl -> do 
          ats1 <- assumeNP al1
          Schg c1 c4  . normalizeAl <$> mergeAtAl ats1 (denormalizeAl al2)
        Nothing -> Nothing
    -- sChg SCns
    (Nothing, Just Refl) -> do
      case testEquality c1 c3 of
        Just Refl -> do
          ats2 <- assumeNP al2
          -- TODO lets _not_ denormalize here, it's slow. we're just doing it
          -- such that the Agda code is trivially portable, but once we ported
          -- it, we should directly used normal form alignmen. I'm just
          -- very lazy at the moment
          sCns c2 <$> mergeAlAt (denormalizeAl al1) ats2
        Nothing -> Nothing
    -- sChg sChg
    (Nothing, Nothing) -> Nothing


sNatCtx :: forall ki codes p ix xs. IsNat ix => Ctx ki codes p ix xs -> SNat ix
sNatCtx _ = getSNat (Proxy :: Proxy ix)
\end{code}


\subsection{Merging Almus}

We want the following diagram:

      x----->y
      |      |
      |      |
      v      v
      y----->y

\begin{code}
mergeAlmu
  :: forall ki codes ix iy
   . IsNat ix
  => Almu ki codes ix ix
  -> Almu ki codes ix ix
  -> Maybe (Almu ki codes iy ix)
\end{code}

Because we pattern match in |Spn|, we catually learn 
that |ix ~ iy| and the type of |mergeAlmu| becomes easier to deal with.
It infact forces the type to be homogenous, and we know that merging
homogenous patches is possible.
\begin{spec}
mergeAlmu :: Almu iy iy -> Almu iy iy -> Maybe (Almu iy iy)
\end{spec}
\begin{code}
mergeAlmu (Ins c ctx)   (Spn s) =
  doCtxSpn c ctx s
    where
      doCtxSpn
        :: Constr (Lkup iy codes) c
        -> InsCtx ki codes iy (Lkup c (Lkup iy codes))
        -> Spine ki codes (Lkup iy codes)
        -> Maybe (Almu ki codes iy iy)
      doCtxSpn = undefined
\end{code}
\begin{code}
mergeAlmu (Del c ctx)   (Spn s) =
  doCtxSpn c ctx s
    where
      doCtxSpn
        :: Constr (Lkup iy codes) c
        -> DelCtx ki codes iy (Lkup c (Lkup iy codes))
        -> Spine ki codes (Lkup iy codes)
        -> Maybe (Almu ki codes iy iy)
      doCtxSpn = undefined
mergeAlmu (Spn s)       (Ins c ctx) = undefined 
mergeAlmu (Spn s)       (Del c ctx) = undefined
mergeAlmu (Spn s1)      (Spn s2) = Spn <$> mergeSpine s1 s2 
\end{code}
Now we arrive at the more difficult part.  We have 
\begin{spec}
   x :: Almu ix iy
   y :: Almu ix iy
\end{spec}
And we need to reconcile this into  Almu iy iy
But nothing about the patch helps us here.


TODO make a pretty diagram


In order to diff and an Ins,  we have the following diagram
                
Ins               \                Del                   \               
ix|c1|a|b|*|d|    |                iy|c2|e|f|g|*|        |              
          |       | :: Almu ix iy              |         | :: Almu ix iy
          v       |                            v         |              
          x :: iv /                            y :: iw   /              


                         iv ~ iw
---------------------------------------------------------------------
              
              sCns c1 


                                                    \
                 iy|c1|a|b| |d|                     |
                           |                        |  :: Almu iy iy
                           v                        |
                      (merge x y) (Almu :: iw iw)   /

\begin{code}
mergeAlmu (Ins c1 ctx1) y@(Del c2 ctx2) =
  Spn . sCns c1 <$> mergeCtxAlmu ctx1 y
  where
    mergeCtxAlmu
      :: InsCtx ki codes ix  xs
      -> Almu ki codes ix iy
      -> Maybe (NP (At ki codes) xs)
    mergeCtxAlmu (H almu' xs) almu = do
      -- THE IMPORTANT BIT
      Refl <- testEquality (sNatFixIdx almu') (sNatFixIdx almu)
      almu'' <- mergeAlmu almu' almu
      pure $ AtFix almu'' :* (mapNP makeIdAt xs)
    mergeCtxAlmu (T a ctx) almu =  do
      let at = makeIdAt a
      xs <- mergeCtxAlmu ctx almu
      pure $ at :* xs
\end{code}

\begin{code}
mergeAlmu x@(Del c1 ctx1) (Ins c2 ctx2) =
  Ins c2 <$> mergeAlmuCtx x ctx2
  where
    mergeAlmuCtx
      :: Almu ki codes ix iy
      -> InsCtx ki codes ix xs
      -> Maybe (InsCtx ki codes iy xs)
    mergeAlmuCtx almu (H almu' xs) = do
      -- THE IMPORTANT BIT
      Refl <- testEquality (sNatFixIdx almu) (sNatFixIdx almu')
      almu'' <- mergeAlmu almu almu'
      pure $ H almu'' xs
    mergeAlmuCtx almu (T a ctx) = T a  <$> mergeAlmuCtx almu ctx


-- If x == x' and   x' == y'  then we can merge. otherwise Nothing
mergeAlmu (Stiff x y)   (Stiff x' y') = undefined
mergeAlmu (Stiff _ _)   _ = Nothing
mergeAlmu _             (Stiff _ _) = Nothing

-- TODO ACtually if they insert or delete the same thing, they can be reconciled
mergeAlmu (Del _ _)     (Del _ _) = Nothing
mergeAlmu (Ins _ _)     (Ins _ _) = Nothing

\end{code}
