\begin{code}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
module Examples.MergePlayground where
import Data.Maybe (fromJust)
import Generics.MRSOP.Diff2
import Generics.MRSOP.Diff.Merge (mergeAlmu)
import Generics.MRSOP.Base
import Generics.MRSOP.TH
import Generics.MRSOP.Util
import Generics.MRSOP.Opaque

\end{code}


Our very small statement based language
\begin{code}
data Stmt
  = String := Expr
  | Stmt :> Stmt
  | Return Expr

data Expr 
  = Val Int
  | Var String
  | Expr :+: Expr

infixr 3 :>
infixl 8 :=
infixl 9 :+:

type Stmt' = Z
type Expr' = S Z

deriveFamily [t|Stmt|]

\end{code}


And lets add an example:

\begin{code}
code1 :: Stmt
code1 = 
  "x" := Val 0                 :>
  "y" := Val 2                 :>
  "z" := Var "x" :+: Var "y"   :>
  Return (Var "z")
\end{code}

\begin{code}


a :: Almu Singl CodesStmt Expr' Expr'
a = Spn Scp

b :: Almu Singl CodesStmt Expr' Stmt'
b = Ins CZ (T (NA_K (SString "x")) (H a NP0))

c :: Almu Singl CodesStmt Stmt' Stmt'
c = Del CZ (T (NA_K (SString "y")) (H (AlmuMin b) NP0))



a' :: Almu Singl CodesStmt Expr' Expr'
a' = Spn Scp

b' :: Almu Singl CodesStmt Stmt' Expr'
b' = Del CZ (T (NA_K (SString "x")) (H (AlmuMin a') NP0))

c' :: Almu Singl CodesStmt Stmt' Stmt'
c' = Ins CZ (T (NA_K (SString "y")) (H b' NP0))

merged :: Almu Singl CodesStmt Stmt' Stmt'
merged = undefined $ mergeAlmu c c'


\end{code}

