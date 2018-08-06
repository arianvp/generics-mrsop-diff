{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyCase #-}
module Generics.MRSOP.Diff.Merge where

import Data.Type.Equality
import Generics.MRSOP.Util
import Generics.MRSOP.Base
import Generics.MRSOP.Diff2


{-
data MergeResultAlmu ki codes ix :: * where
  Conflict :: Almu ki codes ix
           -> Almu ki codes ix
           -> MergeResultAlmu ki codes ix
  MergeSpn :: 
  
  -}
  

-- TODO: We wanna tell when a conflict occurs
-- some kind of _as far as possible semantics_
-- where we have a hole where we can't continue, and will tell us
-- where in the diff the conflict occured _exactly_
--
--  Almu' =  Almu  (Almu x Almu  | Almu)
--  For this we need to go back to the agda def of Almu, where
--  we can change the Rec parameter but that must be doable
--
--  however for this, the type of Ctx needs to change in the Agda code as well?
--  as currently it's fixed for Almu?
--
-- But for now, we just give a Nothing, so that we have
-- something that works :)


makeIdAt :: NA ki (Fix ki codes) a -> At ki codes a
makeIdAt (NA_I _) = AtFix (Spn Scp)
makeIdAt (NA_K k) = AtSet (Trivial k k)

mergeCtxAlmu ::
     IsNat ix
  => Ctx ki codes ix xs
  -> Almu ki codes ix
  -> Maybe (NP (At ki codes) xs)
mergeCtxAlmu ctx almu =
  case ctx of
    H almu' rest -> do
      x <- mergeAlmu almu almu'
      let rest' = mapNP makeIdAt rest
      pure $ AtFix x :* rest'
    T a ctx' -> do
      xs <- mergeCtxAlmu ctx' almu
      pure $ makeIdAt a :* xs


mergeAlmuCtx :: IsNat ix =>
     Almu ki codes ix -> Ctx ki codes ix xs -> Maybe (Ctx ki codes ix xs)
mergeAlmuCtx almu (H almu' rest) = H <$> mergeAlmu almu almu' <*> pure rest
mergeAlmuCtx almu (T a ctx) = T a <$> mergeAlmuCtx almu ctx

mergeAt :: At ki codes a -> At ki codes a -> Maybe (At ki codes a)
mergeAt (AtSet _) (AtSet k2) =
  -- TODO
  -- if disjoint  then k2
  -- else Nothing
  Just (AtSet k2)
mergeAt (AtFix almu1) (AtFix almu2) = AtFix <$> mergeAlmu almu1 almu2


mergeAts :: NP (At ki codes) xs -> NP (At ki codes) xs -> Maybe (NP (At ki codes) xs)
mergeAts NP0 NP0 = Just NP0
mergeAts (px :* xs) (py :* ys) = (:*) <$> mergeAt px py <*> mergeAts xs ys


-- assumes that this alignment is simply an NP
-- should return a descriptive error message in the future
-- for debugging purposes
assumeNP :: Al ki codes xs xs -> Maybe (NP (At ki codes) xs)
assumeNP (A0 NP0 NP0) = Just NP0
assumeNP (A0 _ _) = Nothing
assumeNP (AX NP0 NP0 px xs) = (px :*) <$> assumeNP xs
assumeNP (AX _ _ _ _ ) = Nothing


{-
  merge-At-Al : ∀{l₁ l₂}(ats : All (At PatchRec) l₁)(al : Al (At PatchRec) l₁ l₂)
             → (hip : disj-At-Al ats al)             
             → Al (At PatchRec) l₁ l₂         
  merge-At-Al []       A0  hip = A0                  
  merge-At-Al []       (Ains at al)  hip = (Ains at al)
  merge-At-Al (a ∷ as) (Ains at al) hip          
    = Ains at (merge-At-Al (a ∷ as) al hip)     
  merge-At-Al (a ∷ as) (Adel at al) (ida , hip)     
    = Adel at (merge-At-Al as al hip)            
  merge-At-Al (a ∷ as) (AX at al)   (ha , hip)       
    = AX (mergeAt a at ha) (merge-At-Al as al hip) -}


-- 



mergeAtAl :: NP (At ki codes) xs -> Al ki codes xs ys -> Maybe (Al ki codes xs ys)

mergeAtAl NP0 al =
 case al of
  A0 NP0 inss -> Just $ A0 NP0 inss
mergeAtAl (_ :* _) _ = undefined

-- assume RHS is an NP

mergeAlAt :: Al ki codes xs ys -> NP (At ki codes) xs -> Maybe (NP (At ki codes) ys)
mergeAlAt = undefined

mergeSpine ::
     Spine ki codes xs -> Spine ki codes xs -> Maybe (Spine ki codes xs)
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
          Schg c1 c4  <$> mergeAtAl ats1 al2
        Nothing -> Nothing
    -- sChg SCns
    (Nothing, Just Refl) -> do
      case testEquality c1 c3 of
        Just Refl -> do
          ats2 <- assumeNP al2
          sCns c2 <$> mergeAlAt al1 ats2
        Nothing -> Nothing
    -- sChg sChg
    (Nothing, Nothing) -> Nothing

mergeAlmu :: IsNat ix => Almu ki codes ix -> Almu ki codes ix -> Maybe (Almu ki codes ix)
mergeAlmu (Ins _ _) (Ins _ _) = Nothing
mergeAlmu (Ins c ctx) almu@(Spn _) = Spn . sCns c <$> mergeCtxAlmu ctx almu
mergeAlmu (Ins c1 ctx1) almu@(Del _ _) =
  Spn . sCns c1 <$> mergeCtxAlmu ctx1 almu
mergeAlmu almu@(Spn _) (Ins c ctx) = Ins c <$> mergeAlmuCtx almu ctx
mergeAlmu (Spn s1) (Spn s2) = Spn <$> mergeSpine s1 s2
mergeAlmu (Spn _) (Del _ _) = undefined
mergeAlmu (Del _ _) (Del _ _) = Nothing
mergeAlmu (Del _ _) (Ins _ _) = undefined
mergeAlmu (Del _ _) (Spn _) = undefined
