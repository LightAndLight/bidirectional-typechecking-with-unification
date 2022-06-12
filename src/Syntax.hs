module Syntax where

import Name (Name (..))
import Type (Ty (..))

data Expr
  = Var Name
  | Ann Expr Ty
  | Lam Name (Maybe Ty) Expr
  | App Expr Expr
  | LamTy Name Expr
  | AppTy Expr Ty
  | Pack Name Ty Expr
  | Unpack (Name, Name, Expr) Expr
  | Number Integer
  | Pair Expr Expr
  | Fst Expr
  | Snd Expr
  | Inl Expr
  | Inr Expr
  | Bool Bool
  deriving (Eq, Show)

elim :: Expr -> Expr -> Expr -> Expr
elim f g = App (App (App (Var (Name "elim")) f) g)