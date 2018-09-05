{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Clojure.AST where

import Data.Type.Equality

import Data.Text
import Data.Text.Encoding (encodeUtf8)
import Generics.MRSOP.TH
import Generics.MRSOP.Base
import Generics.MRSOP.Util hiding (Cons, Nil)
import Data.Digems.Generic.Digest


data SepOldExprList =
   Nil 
 | Cons OldExpr !Sep SepOldExprList 
 deriving (Show)

data Sep = Space | Comma | NewLine | EmptySep deriving (Show, Eq)

-- A non-mutual-recursive "cannonical" version of OldExpr
-- We use this because mutual recursion diffs are currently 'broken'
data Expr 
  = CSpecial !FormTy Expr
  | CDispatch Expr
  | CTerm Term
  | CComment !Text
  | CCons !CollTy Expr !Sep Expr
  | CNil !CollTy
  deriving (Show)


cannonList :: CollTy -> SepOldExprList -> Expr
cannonList ty Nil = CNil ty
cannonList ty (Cons expr sep xs) = CCons ty (cannon expr) sep (cannonList ty xs)

-- cannonicalizes non-toplevel expressions
cannon :: OldExpr -> Expr
cannon (Seq a b) = error "should only occur on toplevel"
cannon Empty     = error "should only occur on toplevel"
cannon (Special a b) = CSpecial a (cannon b)
cannon (Dispatch a) = CDispatch (cannon a)
cannon (Term a) = CTerm a
cannon (Comment a) = CComment a
cannon (Collection colTy xs) = cannonList colTy xs

cannonTopLevel :: OldExpr -> Expr
-- TODO 'NewLine' is not totally correct
cannonTopLevel (Seq e1 e2) = 
  CCons TopLevel (cannon e1) NewLine (cannonTopLevel e2)
cannonTopLevel Empty = CNil TopLevel

data OldExpr = Special !FormTy OldExpr 
          | Dispatch OldExpr 
          | Collection !CollTy SepOldExprList 
          | Term Term 
          | Comment !Text 
          | Seq OldExpr OldExpr 
          | Empty 
          deriving (Show)

data FormTy = Quote | SQuote | UnQuote | DeRef | Meta deriving (Show, Eq)

data CollTy = TopLevel | Vec | Set | Parens deriving (Show, Eq)

data Term = TaggedString !Tag !Text 
  deriving (Show)

data Tag = String | Var  deriving (Show, Eq)



data ConflictResult a = NoConflict | ConflictAt a
  deriving (Show, Eq)

data CljKon = CljText
data CljSingl (kon :: CljKon) :: * where
  SCljText :: Text -> CljSingl CljText

instance Digestible Text where
  digest = hash . encodeUtf8

instance Digestible1 CljSingl where
  digest1 (SCljText text) = digest text
  

deriving instance Show (CljSingl k)
deriving instance Eq (CljSingl k)
instance Show1 CljSingl where show1 = show
instance Eq1 CljSingl where eq1 = (==)

instance TestEquality CljSingl where
  testEquality (SCljText _) (SCljText _) = Just Refl


deriveFamilyWith ''CljSingl [t| Expr |]
