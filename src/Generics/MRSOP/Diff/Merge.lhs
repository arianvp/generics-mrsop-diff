\begin{code}
{-# OPTIONS_GHC -Wall -Wno-unused-matches -Wno-name-shadowing #-}
module Generics.MRSOP.Diff.Merge where

import Data.Proxy
import Data.Type.Equality
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Diff2

data MergeError = Failed | DelDel | InsIns deriving Show

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither = flip maybe Right . Left

data Merged (ki :: kon -> *) (codes :: [[[Atom kon]]]) (ix :: Nat) :: * where
  Merged :: Almu ki codes ix iy -> Merged ki codes ix

-- assumes that this alignment is simply an NP
-- should return a descriptive error message in the future
-- for debugging purposes
assumeNP :: Al ki codes xs xs -> Either [MergeError] (NP (At ki codes) xs)
assumeNP (A0 NP0 NP0) = Right NP0
assumeNP (A0 _ _) = Left [Failed]
assumeNP (AX NP0 (_ :* _) _ _) = Left [Failed]
assumeNP (AX (_ :* _) _ _ _) = Left [Failed]
assumeNP (AX NP0 NP0 px xs) = (px :*) <$> assumeNP xs


makeIdAt :: NA ki (Fix ki codes) a -> At ki codes a
makeIdAt (NA_I _) = AtFix (Spn Scp)
makeIdAt (NA_K k) = AtSet (Trivial k k)

{-mergeAtCtx
  :: NP (At ki codes) xs
  -> Ctx ki codes (Almu ki codes) ix xs
  -> Either [MergeError] (Ctx ki codes (Almu ki codes) ix xs)
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
  -> Either [MergeError] (Almu ki codes ix ix)
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
  -> Either [MergeError] (NP (At ki codes) (Lkup c (Lkup ix codes)))
mergeCtxAlmu c (H almu' xs) almu =
  case testEquality (getSource almu) (getTarget almu') of
    Just Refl -> do
      x <- mergeAlmu almu almu'
      let xs' = mapNP makeIdAt xs
      pure $ AtFix x :* xs'
    Left [Failed] -> Left [Failed]
mergeCtxAlmu c (T a ctx) almu = do
  let a' =  makeIdAt a 
  xs' <- mergeCtxAlmu  ctx almu 
  pure $ a' :* xs'

mergeAlmuCtx
  :: (IsNat ix, IsNat iy)
  => Almu ki codes ix iy
  -> InsCtx ki codes ix xs
  -> Either [MergeError] (InsCtx ki codes ix xs)
mergeAlmuCtx almu (H almu' rest) =
  case testEquality (sNatFixIdx almu) (sNatFixIdx almu') of
    Just Refl -> do
      almu'' <- mergeAlmu almu almu'
      pure $ H almu'' rest
    Left [Failed] -> Left [Failed]
mergeAlmuCtx almu (T a ctx) = T a <$> mergeAlmuCtx almu ctx
-}


mergeAlAt
  :: Eq1 ki
  => AlOld ki codes xs ys 
  -> NP (At ki codes) xs
  -> Either [MergeError] (NP (At ki codes) ys)
mergeAlAt OA0 NP0 =  pure NP0
mergeAlAt (OAIns at al) NP0 = (:*) <$> pure (makeIdAt at) <*> mergeAlAt al NP0
mergeAlAt (OAIns at al) (a :* as) = (:*) <$> pure (makeIdAt at) <*> mergeAlAt al (a :* as)
mergeAlAt (OADel at al) (a :* as) = mergeAlAt al as
mergeAlAt (OAX at al) (a :* as) = (:*) <$> mergeAt at a <*> mergeAlAt al as

mergeAtAl
  :: Eq1 ki
  => NP (At ki codes) xs
  -> AlOld ki codes xs ys
  -> Either [MergeError] (AlOld ki codes xs ys)
mergeAtAl at al =
  case (at, al) of
    (NP0, OA0) -> pure OA0
    (NP0, OAIns at' al') -> pure $ OAIns at' al'
    (a :* as, OAIns at' al') -> OAIns at' <$> mergeAtAl (a :* as) al'
    (a :* as, OADel at' al') -> OADel at' <$> mergeAtAl as al'
    (a :* as, OAX at' al') -> OAX <$> mergeAt a at' <*> mergeAtAl as al'

mergeAt :: Eq1 ki => At ki codes a -> At ki codes a -> Either [MergeError] (At ki codes a)
mergeAt (AtSet _) (AtSet k2) =
  -- TODO TODO TODO TODO
  -- if disjoint  then k2
  -- else Left [Failed]
  pure (AtSet k2)
mergeAt (AtFix almu1) (AtFix almu2) = do
  let x = sNatFixIdx almu1 
  let y = sNatFixIdx almu2
  case testEquality x y of
    Just Refl -> do
      almu <- mergeAlmu almu1 almu2
      pure $ AtFix almu
    Nothing -> Left [Failed]

mergeAts
  :: Eq1 ki
  => NP (At ki codes) xs 
  -> NP (At ki codes) xs 
  -> Either [MergeError] (NP (At ki codes) xs)
mergeAts NP0 NP0 = Right NP0
mergeAts (px :* xs) (py :* ys) = (:*) <$> mergeAt px py <*> mergeAts xs ys


mergeSpine
  :: Eq1 ki
  => Spine ki codes xs
  -> Spine ki codes xs 
  -> Either [MergeError] (Spine ki codes xs)
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
        Nothing-> Left [Failed]
    -- sCns   sChg
    --
    -- sChg c1 c1    sChg c2 c3
    -- 
    (Just Refl, Nothing) -> do
      case testEquality c1 c3 of
        Just Refl -> do 
          ats1 <- assumeNP al1
          Schg c1 c4  . normalizeAl <$> mergeAtAl ats1 (denormalizeAl al2)
        Nothing-> Left [Failed]
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
        Nothing -> Left [Failed]
    -- sChg sChg
    (Nothing, Nothing) -> Left [Failed]


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
   . (IsNat ix, IsNat iy, Eq1 ki)
  => Almu ki codes ix iy
  -> Almu ki codes ix iy
  -> Either [MergeError] (Almu ki codes iy iy)
\end{code}

Because we pattern match in |Spn|, we catually learn 
that |ix ~ iy| and the type of |mergeAlmu| becomes easier to deal with.
It infact forces the type to be homogenous, and we know that merging
homogenous patches is possible.
\begin{spec}
mergeAlmu :: Almu iy iy -> Almu iy iy -> Either [MergeError] (Almu iy iy)
\end{spec}
\begin{code}
mergeAlmu (Ins c ctx)   (Spn s) =
  doCtxSpn c ctx s
    where
      doCtxSpn
        :: Constr (Lkup iy codes) c
        -> InsCtx ki codes iy (Lkup c (Lkup iy codes))
        -> Spine ki codes (Lkup iy codes)
        -> Either [MergeError] (Almu ki codes iy iy)
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
        -> Either [MergeError] (Almu ki codes iy iy)
      doCtxSpn = undefined
mergeAlmu (Spn s)       (Ins c ctx) = undefined 
mergeAlmu (Spn s)       (Del c ctx) = _
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
  Del c1 <$> mergeInsDel y ctx1
  where
    mergeInsDel
      :: Almu ki codes ix iy
      -> InsCtx ki codes ix ys
      -> Either [MergeError] (DelCtx ki codes iy ys)
    mergeInsDel almu (H almu' xs) =  do
      -- if the two patches have the same destination, we can merge them
      Refl <- maybeToEither [Failed] $ testEquality (sNatFixIdx almu) (sNatFixIdx almu')
      almu'' <- mergeAlmu almu almu'
      pure $ H (AlmuMin almu'') xs
    mergeInsDel almu (T a ctx) = T a <$> mergeInsDel almu ctx
{-
mergeAlmu (Ins c1 ctx1) y@(Del c2 ctx2) =
  -- TODO Why not the dual here?   Del $ Ins ?
  -- why do we 'change' the patch?
  Spn . sCns c1 <$> mergeCtxAlmu ctx1 y
  where
    mergeCtxAlmu
      :: InsCtx ki codes ix  xs
      -> Almu ki codes ix iy
      -> Either [MergeError] (NP (At ki codes) xs)
    mergeCtxAlmu (H almu' xs) almu = do
      -- THE IMPORTANT BIT
      Refl <- maybeToEither [Failed] $ testEquality (sNatFixIdx almu') (sNatFixIdx almu)
      almu'' <- mergeAlmu almu' almu
      pure $ AtFix almu'' :* (mapNP makeIdAt xs)
    mergeCtxAlmu (T a ctx) almu =  do
      let at = makeIdAt a
      xs <- mergeCtxAlmu ctx almu
      pure $ at :* xs
-}
\end{code}

\begin{code}
mergeAlmu x@(Del c1 ctx1) (Ins c2 ctx2) =
  Ins c2 <$> mergeDelIns x ctx2
  where
    mergeDelIns
      :: Almu ki codes ix iy
      -> InsCtx ki codes ix xs
      -> Either [MergeError] (InsCtx ki codes iy xs)
    mergeDelIns almu (H almu' xs) = do
      -- THE IMPORTANT BIT
      Refl <- maybeToEither [Failed] $ testEquality (sNatFixIdx almu) (sNatFixIdx almu')
      almu'' <- mergeAlmu almu almu'
      pure $ H almu'' xs
    mergeDelIns almu (T a ctx) = T a  <$> mergeDelIns almu ctx


-- If x == x' and   x' == y'  then we can merge. otherwise Left [Failed]

-- However, this might be too restrictive? I'm not sure. We might
-- not want to care at the atoms. "Structural disjointness"
mergeAlmu (Stiff x y)   (Stiff x' y') = do
  let tx = sNatFixIdx x
  let ty = sNatFixIdx y
  let ty' = sNatFixIdx y'
  Refl <- maybeToEither [Failed] (testEquality ty ty')
  Refl <- maybeToEither [Failed] (testEquality tx ty)
  -- TODO we should do a structural equality test here instead.
  if eq1 x x' && eq1 y y'
  then pure (Stiff x' y')
  else Left [Failed]
mergeAlmu (Stiff _ _)   _ = Left [Failed]
mergeAlmu _             (Stiff _ _) = Left [Failed]

-- TODO ACtually if they insert or delete the same thing, they can be reconciled
-- This is when we talk about the 'structural disjointness'
mergeAlmu (Del _ _)     (Del _ _) = Left [DelDel]
mergeAlmu (Ins _ _)     (Ins _ _) = Left [InsIns]

\end{code}