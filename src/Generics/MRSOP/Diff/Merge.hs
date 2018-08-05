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
makeIdAt (NA_I i) = AtFix (Spn Scp)
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
    T a ctx -> do
      xs <- mergeCtxAlmu ctx almu
      pure $ makeIdAt a :* xs


mergeAlmuCtx :: IsNat ix =>
     Almu ki codes ix -> Ctx ki codes ix xs -> Maybe (Ctx ki codes ix xs)
mergeAlmuCtx almu (H almu' rest) = H <$> mergeAlmu almu almu' <*> pure rest
mergeAlmuCtx almu (T a ctx) = T a <$> mergeAlmuCtx almu ctx

mergeAt :: At ki codes a -> At ki codes a -> Maybe (At ki codes a)
mergeAt (AtSet k1) (AtSet k2) =
  -- TODO
  -- if disjoint  then k2
  -- else Nothing
  Just (AtSet k2)
mergeAt (AtFix almu1) (AtFix almu2) = AtFix <$> mergeAlmu almu1 almu2

-- TODO make less partial, explain
--
-- We're actually looking for  NP (At) here but we trew away
-- that info
mergeAX :: Al ki codes xs xs -> Al ki codes xs xs -> Maybe (Al ki codes xs xs)
mergeAX (A0 NP0 NP0) (A0 NP0 NP0) = Just $ A0 NP0 NP0
mergeAX (A0 _ _) (A0 _ _) = Nothing -- TODO descriptive error message
mergeAX (AX NP0 NP0 px xs) (AX NP0 NP0 py ys) =
  AX NP0 NP0 <$> (mergeAt px py) <*> mergeAX xs ys
mergeAX (AX _ _ _ _) (AX _ _ _ _) = Nothing -- TODO descriptive error message


--        Assume it's an NP   
mergeR :: Al ki codes xs xs ->  Al ki codes xs ys  -> Maybe (Al ki codes xs ys)
mergeR = undefined

mergeL :: Al ki codes xs ys ->  Al ki codes xs xs -> Maybe (Al ki codes xs xs)
mergeL = undefined

mergeSpine ::
     Spine ki codes xs -> Spine ki codes xs -> Maybe (Spine ki codes xs)
mergeSpine Scp s = pure s
mergeSpine s Scp = pure s
mergeSpine (Schg c1 c2 al1) (Schg c3 c4 al2) =
  -- sCns sCns
  case (testEquality c1 c2, testEquality c3 c4) of
    (Just Refl, Just Refl) ->
      case testEquality c1 c3 of
        Just Refl -> Schg c1 c1 <$> mergeAX al1 al2
        Nothing -> Nothing
    -- sCns   sChg
    (Just Refl, Nothing) -> 
      case testEquality c1 c3 of
        Just Refl -> Schg c1 c4 <$> mergeR al1 al2
        Nothing -> Nothing
    -- sChg SCns
    (Nothing, Just Refl) ->
      case testEquality c1 c3 of
        Just Refl -> Schg c1 c1 <$> mergeL al1 al2
        Nothing -> Nothing
    (Nothing, Nothing) -> Nothing


mergeAlmu :: IsNat ix => Almu ki codes ix -> Almu ki codes ix -> Maybe (Almu ki codes ix)
mergeAlmu (Ins _ _) (Ins _ _) = Nothing
mergeAlmu (Ins c ctx) almu@(Spn s) = Spn . sCns c <$> mergeCtxAlmu ctx almu
mergeAlmu (Ins c1 ctx1) almu@(Del c2 ctx2) =
  Spn . sCns c1 <$> mergeCtxAlmu ctx1 almu
mergeAlmu almu@(Spn s) (Ins c ctx) = Ins c <$> mergeAlmuCtx almu ctx
mergeAlmu (Spn s1) (Spn s2) = Spn <$> mergeSpine s1 s2
mergeAlmu (Spn _) (Del _ _) = undefined
mergeAlmu (Del _ _) (Del _ _) = Nothing
mergeAlmu (Del _ _) (Ins _ _) = undefined
mergeAlmu (Del _ _) (Spn _) = undefined
