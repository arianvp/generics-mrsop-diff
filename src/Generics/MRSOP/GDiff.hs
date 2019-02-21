{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}

module Generics.MRSOP.GDiff where

import Debug.Trace
import GHC.Exts hiding (IsList)

import Control.Monad
import Data.Proxy
import Data.Functor.Const
import Data.Semigroup
import Data.Type.Equality
import Generics.MRSOP.Base hiding (listPrfNP)
import Generics.MRSOP.Base.Metadata
import Generics.MRSOP.GDiff.Util
import Generics.MRSOP.Util (Nat, Eq1(eq1), IsNat, (:++:), Lkup, Show1(show1), Idx, El(El), getSNat)

import qualified Generics.MRSOP.AG as AG

-- | Either a type index and constructor index, OR a constant
data Cof (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: Atom kon -> [Atom kon] -> * where
  -- ^ A constructor tells us the type of its arguments and which type in the family it constructs
  ConstrI :: (IsNat c, IsNat n) => Constr (Lkup n codes) c -> ListPrf (Lkup c (Lkup n codes)) -> Cof ki codes (I n) (Lkup c (Lkup n codes))

  -- ^ Requires no arguments to complete
  ConstrK :: ki k -> Cof ki codes (K k) '[]

data ES (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  ES0 :: ES ki codes '[] '[]
  Ins :: Int -> Cof ki codes a t -> ES ki codes i          (t :++: j) -> ES ki codes i        (a ': j)
  Del :: Int -> Cof ki codes a t -> ES ki codes (t :++: i) j          -> ES ki codes (a ': i) j
  Cpy :: Int -> Cof ki codes a t -> ES ki codes (t :++: i) (t :++: j) -> ES ki codes (a ': i) (a ': j)

  -- optimization, Copy over an atom in its entirety because we know they're deeply equal
  CpyTree :: Int -> ES ki codes i j -> ES ki codes (a ': i) (a ': j)



cofWitnessI :: Cof ki codes (I n) t -> Proxy n
cofWitnessI _ = Proxy
  
heqCof ::
     (Eq1 ki, TestEquality ki)
  => Cof ki codes a cx
  -> Cof ki codes b cy
  -> Maybe (a :~: b, cx :~: cy)
heqCof cx@(ConstrI x _) cy@(ConstrI y _) =
  case testEquality (getSNat (cofWitnessI cx)) (getSNat (cofWitnessI cy)) of
    Nothing -> Nothing
    Just Refl ->
      case testEquality x y of
        Nothing -> Nothing
        Just Refl -> Just (Refl, Refl)
heqCof (ConstrK x) (ConstrK y) =
  case testEquality x y of
    Just Refl ->
      if eq1 x y
        then Just (Refl, Refl)
        else Nothing
    Nothing -> Nothing
heqCof _ _ = Nothing

    

-- {-# INLINE cost #-}
--
--  IDEA: Instead of calculating cost every time (Expensive)
--  build up cost by construction (We get it for free)
cost :: ES ki codes txs tys -> Int
cost ES0 = 0
cost (Ins k c es) = k
cost (Del k c es) = k
cost (Cpy k c es) = k
cost (CpyTree k es) = k

-- {-# INLINE meet #-}
meet :: ES ki codes txs tys -> ES ki codes txs tys -> ES ki codes txs tys
meet d1 d2 =
  if cost d1 <= cost d2
    then d1
    else d2

data EST (ki :: kon -> *) (codes :: [[[Atom kon]]]) :: [Atom kon] -> [Atom kon] -> * where
  NN :: ES ki codes '[] '[] 
     -> EST ki codes '[] '[]
  NC :: Cof ki codes y t
     -> ES ki codes '[] (y ': tys)
     -> EST ki codes '[] (t :++: tys)
     -> EST ki codes '[] (y ': tys)
  CN :: Cof ki codes x t
     -> ES ki codes (x ': txs) '[]
     -> EST ki codes (t :++: txs) '[]
     -> EST ki codes (x ': txs) '[]
  CC :: Cof ki codes x t1
     -> Cof ki codes y t2
     -> ES ki codes (x ': txs) (y ': tys)
     -> EST ki codes (x ': txs) (t2 :++: tys)
     -> EST ki codes (t1 :++: txs) (y ': tys)
     -> EST ki codes (t1:++: txs) (t2 :++: tys)
     -> EST ki codes (x ': txs) (y ': tys)


getDiff :: EST ki codes rxs rys -> ES ki codes rxs rys
getDiff (NN x) = x
getDiff (NC _ x _) = x
getDiff (CN _ x _) = x
getDiff (CC _ _ x _ _ _) = x


-- existential version of Cof, that hides c
data Match ki phi codes a where
  Match :: Cof ki codes a t -> PoA ki (AnnFix ki codes phi) t -> Match ki phi codes a

-- | Non-CC version of matchConstructor
--
-- A version of sop but over NA instead of Rep
matchC :: NA ki (AnnFix ki codes phi) a -> Match ki phi codes a
matchC (NA_K k) = Match (ConstrK k) NP0
matchC (NA_I (AnnFix _ (sop -> Tag c poa))) = Match (ConstrI c (listPrfNP poa)) poa

newtype Oracle phi = Oracle (forall ix. phi ix -> phi ix -> Bool)

diffT 
  :: (Eq1 ki, TestEquality ki)
  => Maybe (Oracle phi)
  -> PoA ki (AnnFix ki codes phi) xs
  -> PoA ki (AnnFix ki codes phi) ys
  -> EST ki codes xs ys
diffT o NP0 NP0 = NN ES0
diffT o ((matchC -> Match c poa) :* xs) NP0 =
  let d = diffT o (appendNP poa xs) NP0
  in CN c (Del (1 + cost (getDiff d)) c (getDiff d)) d
diffT o NP0 ((matchC -> Match c poa) :* ys) =
  let i = diffT o NP0 (appendNP poa ys)
  in NC c (Ins (1 + cost (getDiff i)) c (getDiff i)) i
diffT o ((matchC -> Match c1 poa1) :* xs) ((matchC -> Match c2 poa2) :* ys) =
  let 
    i = extendi c1 c
    d = extendd c2 c
    c = diffT o (appendNP poa1 xs) (appendNP poa2 ys)
    es = bestDiffT c1 c2 i d c
  in CC c1 c2 es i d c

extendi 
  :: (Eq1 ki, TestEquality ki)
  => Cof ki codes x t
  -> EST ki codes (t :++: xs) ys
  -> EST ki codes (x ': xs) ys
extendi = undefined






extendd
  :: Cof ki codes y t
  -> EST ki codes xs (t :++: ys)
  -> EST ki codes xs (y ': ys)
extendd = undefined

bestDiffT
  :: (Eq1 ki, TestEquality ki)
  => Cof ki codes x t1
  -> Cof ki codes y t2
  -> EST ki codes (x ': xs) (t2 :++: ys)
  -> EST ki codes (t1 :++: xs) (y ': ys)
  -> EST ki codes (t1 :++: xs) (t2 :++: ys)
  -> ES ki codes (x ': xs) (y ': ys)
bestDiffT cx cy i d c =
  case heqCof cx cy of
    Just (Refl, Refl) ->
      let c' = getDiff c
      in Cpy (cost c') cx c'
    Nothing -> 
      let
        i' = getDiff i
        d' = getDiff d
      in
        meet (Ins (1 + cost i') cy i') (Del (1 + cost d') cx d')
          
        
-- In Agda this would be:
-- ++⁻ : {A : Set}
--       {P : A -> Set}
--       (xs : List A)
--       {ys : List A} 
--     → All P (xs ++ ys) → All P xs × All P ys
-- ++⁻ []       p          = [] , p
-- ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (px ∷_) id (++⁻ _ pxs)
--
--   Note in particular, that xs is not an implicit argument,
--   and that we explicitly pattern match on it.
--
--   In haskell, types and values are separated, but we can 
--   carry around the Singleton LstPrf in order to
--   discover on the type-level the list, by pattern matching
split :: ListPrf xs -> NP p (xs :++: ys) -> (NP p xs, NP p ys)
split Nil poa = (NP0, poa)
split (Cons p) (x :* rs) =
  let (xs, rest) = split p rs
   in (x :* xs, rest)


matchCof ::
     (Eq1 ki)
  => Cof ki codes a t
  -> NA ki (Fix ki codes) a
  -> Maybe (PoA ki (Fix ki codes) t)
matchCof (ConstrI c1 prf) (NA_I (Fix x)) = match c1 x
matchCof (ConstrK k) (NA_K k2) = guard (eq1 k k2) >> Just NP0

-- we need to give Haskell a bit of a hint that Tyof codes c reduces to an IsList
-- insCof is also really the only place where we _need_ IsList I think
insCof 
  :: Cof ki codes a t
  -> PoA ki (Fix ki codes) (t :++: xs)
  -> PoA ki (Fix ki codes) (a ': xs)
insCof (ConstrI c ispoa) xs =
  let (poa, xs') = split ispoa xs
   in NA_I (Fix $ inj c poa) :* xs'
insCof (ConstrK k) xs = NA_K k :* xs 

delCof ::
     Eq1 ki
  => Cof ki codes a t
  -> PoA ki (Fix ki codes) (a ': xs)
  -> Maybe (PoA ki (Fix ki codes) (t :++: xs))
delCof c (x :* xs) = flip appendNP xs <$> matchCof c x


apply ::
     forall ki fam codes ty1 ty2 ix1 ix2.
     ( Family ki fam codes
     , ix1 ~ Idx ty1 fam
     , ix2 ~ Idx ty2 fam
     , Lkup ix1 fam ~ ty1
     , Lkup ix2 fam ~ ty2
     , IsNat ix1
     , IsNat ix2
     ,  Eq1 ki
     , TestEquality ki
     )
  => ES ki codes '[ 'I ix1] '[ 'I ix2]
  -> ty1
  -> Maybe ty2
apply es a =
  case apply' es (deep a) of
    Just (Fix x) ->
      case dto @ix2 x of
        El b -> Just b
    Nothing -> Nothing

apply' ::
     (IsNat ix1, IsNat ix2,  Eq1 ki)
  => ES ki codes '[ 'I ix1] '[ 'I ix2]
  -> Fix ki codes ix1
  -> Maybe (Fix ki codes ix2)
apply' es x = do
  x <- applyES es (NA_I x :* NP0)
  case x of
    (NA_I y :* NP0) -> pure y

applyES ::
     Eq1 ki
  => ES ki codes xs ys
  -> PoA ki (Fix ki codes) xs
  -> Maybe (PoA ki (Fix ki codes) ys)
applyES ES0 x = Just NP0
applyES (Ins _ c es) xs = insCof c <$> applyES es xs
applyES (Del _ c es) xs = delCof c xs >>= applyES es
applyES (Cpy _ c es) xs = insCof c <$> (delCof c xs >>= applyES es)


{-
-- When Showing, we do not know what the family that we're showing is,
-- as edit scripts are not parameterised over the family.
-- hence, we can not get the datatype info
showCof ::
     (HasDatatypeInfo ki fam codes, Show1 ki) => Cof ki codes a c -> String
showCof (ConstrK k) = show1 k
showCof (ConstrI c) = show c

instance (HasDatatypeInfo ki fam codes, Show1 ki) =>
         Show (ES ki codes xs ys) where
  show ES0 = "ES0"
  show (Ins _ _ _ c d) = "Ins " ++ showCof c ++ " $ " ++ show d
  show (Del _ _ _ c d) = "Del " ++ showCof c ++ " $ " ++ show d
  show (Cpy _ _ _ _ c d) = "Cpy " ++ showCof c ++ " $ " ++ show d



diff :: forall fam ki codes ix1 ix2 ty1 ty2.
     ( Family ki fam codes
     , ix1 ~ Idx ty1 fam
     , ix2 ~ Idx ty2 fam
     , Lkup ix1 fam ~ ty1
     , Lkup ix2 fam ~ ty2
     , IsNat ix1
     , IsNat ix2
     ,  Eq1 ki
     , TestEquality ki
     )
  => ty1
  -> ty2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff a b = diff' (deep a) (deep b)

diff' ::
     ( Eq1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> ES ki codes '[ 'I ix1] '[ 'I ix2]
diff' a b = getDiff $ diff'' a b


-- in order to match a constructor of an Atom
-- we will try all possible constructors, and once we find one that
-- matches, we tell you which constructor it was,
-- and a proof that that it's indeed of the correct type
--
--
--   The gdiff lib wants a   ListPrf (tyof codes c)
--   but we have a NP p (Tyof codes c)
--
--   however, we can't make a function   NP p xs -> ListPrf xs
--   as the constructors of NP don't carry the List proof
--

matchConstructor ::
     NA ki (AnnFix ki codes phi) a
  -> (forall c. Cof ki codes a c -> ListPrf (Tyof codes c) -> PoA ki (AnnFix ki codes phi) (Tyof codes c) -> r)
  -> r
matchConstructor (NA_K k) f = f (ConstrK k) Nil NP0
matchConstructor (NA_I (AnnFix _ rep)) f =
  case sop rep of
    Tag c poa -> f (ConstrI c) (listPrfNP poa) poa

-- | Given two deep representations, we get the diff.
-- Here I simply wrap in a List of Atoms, to use diffT, but I'm not sure if I'm right to do so
-- TODO: ask victor
diff'' ::
     ( Eq1 ki, IsNat ix1, IsNat ix2, TestEquality ki)
  => Fix ki codes ix1
  -> Fix ki codes ix2
  -> EST ki codes '[ 'I ix1] '[ 'I ix2]
diff'' x y =
  let x' = NA_I x
      y' = NA_I y
   in diffA x' y'

diffA ::
     ( Eq1 ki, TestEquality ki)
  => NA ki (AnnFix ki codes phi) x
  -> NA ki (AnnFix ki codes phi) y
  -> EST ki codes '[ x] '[ y]
diffA a b = diffPoA (a :* NP0) (b :* NP0)

diffPoA ::
     ( Eq1 ki, TestEquality ki)
  => PoA ki (AnnFix ki codes phi) '[ x]
  -> PoA ki (AnnFix ki codes phi) '[ y]
  -> EST ki codes '[ x] '[ y]
diffPoA = diffT


diffT' ::
     ( Eq1 ki, TestEquality ki)
  => ListPrf xs
  -> ListPrf ys
  -> PoA ki (AnnFix ki codes phi) xs
  -> PoA ki (AnnFix ki codes phi) ys
  -> EST ki codes xs ys
diffT' Nil Nil NP0 NP0 = NN ES0
diffT' (Cons isxs) Nil (x :* xs) NP0 =
  matchConstructor x $ \cx isxs' xs' ->
    let d = diffT' (appendIsListLemma isxs' isxs) Nil (appendNP xs' xs) NP0
        d' = getDiff d
     in cn isxs isxs' cx (del isxs isxs' (1 + cost d') cx d') d
      -- TODO(1) use smart constructors! CN c (Del c (getDiff d)) d
diffT' Nil (Cons isys) NP0 (y :* ys) =
  matchConstructor y $ \c isys' ys' ->
    let i = diffT' Nil (appendIsListLemma isys' isys) NP0 (appendNP ys' ys)
        i' = getDiff i 
     in nc isys isys' c (ins isys isys' (1 + cost i') c i') i
diffT' (Cons isxs) (Cons isys) (x :* xs) (y :* ys) =
  matchConstructor x $ \cx isxs' xs' ->
    matchConstructor y $ \cy isys' ys' ->
      let i = extendi isxs' isxs cx c
          d = extendd isys' isys cy c
          -- NOTE, c is shared to calculate i and d!
          c =
            diffT'
              (appendIsListLemma isxs' isxs)
              (appendIsListLemma isys' isys)
              (appendNP xs' xs)
              (appendNP ys' ys)
       in cc
            isxs
            isxs'
            isys
            isys'
            cx
            cy
            (bestDiffT cx cy isxs isxs' isys isys' i d c)
            i
            d
            c

extendd ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cy)
  -> ListPrf ys
  -> Cof ki codes y cy
  -> EST ki codes xs (Tyof codes cy :++: ys)
  -> EST ki codes xs (y ': ys)
extendd isys' isys cy dt@(NN d) = nc isys isys' cy (ins isys isys' (1 + cost d) cy d) dt
extendd isys' isys cy dt@(NC _ _  _ d _) = nc isys isys' cy (ins isys isys' (1 + cost d) cy d) dt
extendd isys' isys cy dt@(CN _ _ _ _ _) = extendd' isys' isys cy dt
extendd isys' isys cy dt@(CC _ _ _ _ _ _ _ _ _ _) = extendd' isys' isys cy dt

extendd' ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cy)
  -> ListPrf ys
  -> Cof ki codes y cy
  -> EST ki codes (x ': xs) (Tyof codes cy :++: ys)
  -> EST ki codes (x ': xs) (y ': ys)
extendd' isys' isys cy dt =
  extractd dt $ \isxs' isxs cx dt' ->
    let i = dt
        d = extendd isys' isys cy dt'
        c = dt'
     in cc
          isxs
          isxs'
          isys
          isys'
          cx
          cy
          (bestDiffT cx cy isxs isxs' isys isys' i d c)
          i
          d
          c

extractd ::
     TestEquality ki
  => EST ki codes (x ': xs) ys'
  -> (forall cx. ListPrf (Tyof codes cx) -> ListPrf xs -> Cof ki codes x cx -> EST ki codes (Tyof codes cx :++: xs) ys' -> r)
  -> r
extractd (CC _ isxs _ isys c _ d' _ d _) k = k isxs (sourceTail d') c d
extractd (CN _ isxs c d' d) k = k isxs (sourceTail d') c d

extendi ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cx)
  -> ListPrf xs
  -> Cof ki codes x cx
  -> EST ki codes (Tyof codes cx :++: xs) ys
  -> EST ki codes (x ': xs) ys
extendi isxs' isxs cx dt@(NN d) = cn isxs isxs' cx (del isxs isxs' (1 + cost d) cx d) dt
extendi isxs' isxs cx dt@(CN _ _ _ d _) = cn isxs isxs' cx (del isxs isxs' (1 + cost d) cx d) dt
extendi isxs' isxs cx dt@(NC _ _ _ _ _) = extendi' isxs' isxs cx dt
extendi isxs' isxs cx dt@(CC _ _ _ _ _ _ _ _ _ _) = extendi' isxs' isxs cx dt

extendi' ::
     (Eq1 ki, TestEquality ki)
  => ListPrf (Tyof codes cx)
  -> ListPrf xs
  -> Cof ki codes x cx
  -> EST ki codes (Tyof codes cx :++: xs) (y ': ys)
  -> EST ki codes (x : xs) (y ': ys)
extendi' isxs' isxs cx dt =
  extracti dt $ \isys' isys cy dt' ->
    let i = extendi isxs' isxs cx dt'
        d = dt
        c = dt'
     in cc
          isxs
          isxs'
          isys
          isys'
          cx
          cy
          (bestDiffT cx cy isxs isxs' isys isys' i d c)
          i
          d
          c

cofToListPrf ::
     IsList (Tyof codes cy) => Cof ki codes y cy -> ListPrf (Tyof codes cy)
cofToListPrf _ = listPrf

-- Most time is now spent around marshalling list proofs
-- Question: Do we actually need these list proofs?
sourceTail :: ES ki codes (x ': xs) ys -> ListPrf xs
sourceTail (Ins x y _ _ d) = sourceTail d
sourceTail (Del x y _ _ _) = x
sourceTail (Cpy x y z _ _ _) = x

targetTail :: ES ki codes xs (y ': ys) -> ListPrf ys
targetTail (Ins x y _ _ d) = x
targetTail (Del x y _ _ d) = targetTail d
targetTail (Cpy x y z _ _ _) = y

extracti ::
     (Eq1 ki, TestEquality ki)
  => EST ki codes xs' (y ': ys)
  -> (forall cy. ListPrf (Tyof codes cy)
              -> ListPrf ys
              -> Cof ki codes y cy 
              -> EST ki codes xs' (Tyof codes cy :++: ys) 
              -> r)
  -> r
extracti (CC _ isxs _ isys _ c d i _ _) k = k isys (targetTail d) c i
extracti (NC _ isxs c d i) k = k isxs (targetTail d) c i

bestDiffT ::
     (Eq1 ki, TestEquality ki)
  => Cof ki codes x cx
  -> Cof ki codes y cy
  -> ListPrf xs
  -> ListPrf (Tyof codes cx)
  -> ListPrf ys
  -> ListPrf (Tyof codes cy)
  -> EST ki codes (x ': xs) (Tyof codes cy :++: ys)
  -> EST ki codes (Tyof codes cx :++: xs) (y ': ys)
  -> EST ki codes (Tyof codes cx :++: xs) (Tyof codes cy :++: ys)
  -> ES ki codes (x ': xs) (y ': ys)
bestDiffT cx cy isxs isxs' isys isys' i d c =
  case heqCof cx cy of
    Just (Refl, Refl) ->
      -- TODO: I think this is a bug, we need to consider inserts
      -- or deletes as well? 
      let c' = getDiff c
      in cpy isxs isys isxs' (cost c') cx c' -- cpy isxs' isxs isys cx (getDiff c)
    Nothing ->
      -- TOD: It's wasteful to calculate cost every time. Lets do this instead
      -- costI = getCost (getDiff i)
      -- costD = getCost (getDiff d)
      --
      -- if costI <= costD
      --  then  ins (1 + costI)  (getDiff i)
      --  else  del (1 + costD)  (getDiff d)
      --
      -- this will stop us from calculating cost Over and Over again
      let i' = getDiff i
          d' = getDiff d
      in meet (ins isys isys' (1 + cost i') cy i') (del isxs isxs' (1 + cost d') cx d')

      -}
