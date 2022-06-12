module Syntax where

import qualified Data.List as List
import Data.Word (Word16, Word32, Word64, Word8)
import Name (Name (..))
import Type (Ty (..), substTy)

data Expr
  = Var Name
  | Ann Expr Ty
  | Lam Name (Maybe Ty) Expr
  | App Expr Expr
  | LamTy Name Expr
  | AppTy Expr Ty
  | Pack Name Ty Expr
  | Unpack (Name, Name, Expr) Expr
  | U8 Word8
  | U16 Word16
  | U32 Word32
  | U64 Word64
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