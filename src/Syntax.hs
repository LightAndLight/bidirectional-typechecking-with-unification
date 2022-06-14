module Syntax where

import Data.HashMap.Strict (HashMap)
import Name (Name (..))

data FieldTy
  = Optional Ty
  | Default Ty Expr
  | Required Ty
  deriving (Eq, Show)

data Ty
  = TVar Name
  | TArrow Ty Ty
  | TForall Name Ty
  | TExists Name Ty
  | TPair Ty Ty
  | TSum Ty Ty
  | TU8
  | TU16
  | TU32
  | TU64
  | TBool
  | TRecord (HashMap String FieldTy)
  deriving (Eq, Show)

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