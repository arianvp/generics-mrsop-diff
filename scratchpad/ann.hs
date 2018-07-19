{-# LANGUAGE ScopedTypeVariables, ViewPatterns, DeriveFunctor, DeriveFoldable,
  DeriveTraversable, StandaloneDeriving, UndecidableInstances #-}

import Control.Arrow

newtype Fix f = Fix
  { unFix :: f (Fix f)
  }

deriving instance Show (f (Fix f)) => Show (Fix f)

cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . unFix

-- | Annotate (f r) with attribute a
newtype AnnF f a r =
  AnnF (f r, a)
  deriving (Functor, Show)

-- | Annotated fixed-point type. A cofree comonad.
type Ann f a = Fix (AnnF f a)

-- | Attribute of the root node
attr :: Ann f a -> a
attr (unFix -> AnnF (_, a)) = a

strip :: Ann f a -> f (Ann f a)
strip (unFix -> AnnF (x, _)) = x

-- | strip all attributes
stripAll :: Functor f => Ann f a -> Fix f
stripAll = cata alg
  where


alg (AnnF (x, _)) = Fix x

-- | annotation constructor
ann :: (f (Ann f a), a) -> Ann f a
ann = Fix . AnnF

-- | annotation deconstructor
unAnn :: Ann f a -> (f (Ann f a), a)
unAnn (unFix -> AnnF a) = a

synthesize ::
     forall f a. Functor f
  => (f a -> a)
  -> Fix f
  -> Ann f a
synthesize f = cata alg
  where
    alg :: f (Ann f a) -> Ann f a
    alg = ann . (id &&& f . fmap attr)

data ListF a r
  = C a
      r
  | N
  deriving (Functor, Show, Read)

data ExprF r
  = Const Int
  | Var Id
  | Add r
        r
  | Mul r
        r
  | IfNeg r
          r
          r
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


data Op = Keep | Del deriving Show

-- This is gonna be some annotation function that decides
-- what to keep and what to throw away
annotate :: ExprF a -> Op
annotate (Const x) = Keep
annotate (Var x) = Keep
annotate (Add r1 r2) = Del
annotate (Mul r1 r2) = Keep
annotate (IfNeg r0 r1 r2) = Keep

type Id = String

type Expr = Fix ExprF

e1 =
  Fix
    (Mul
       (Fix
          (IfNeg
             (Fix (Mul (Fix (Const 1)) (Fix (Var "a"))))
             (Fix (Add (Fix (Var "b")) (Fix (Const 0))))
             (Fix (Add (Fix (Var "b")) (Fix (Const 2))))))
       (Fix (Const 3)))

