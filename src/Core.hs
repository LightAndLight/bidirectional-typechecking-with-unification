{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Core where

import Data.Word (Word16, Word32, Word64, Word8)
import Name (Name (..))
import Type (Ty (..), substTy)

data Expr
  = Var Name
  | Ann Expr Ty
  | Lam Name Ty Expr
  | App Expr Expr
  | LamTy Name Expr
  | AppTy Expr Ty
  | Pack Name Ty Expr
  | Unpack (Name, Name, Expr) Expr
  | U8 Word8
  | U16 Word16
  | U32 Word32
  | U64 Word64
  | Pair Expr Expr
  | Fst Expr
  | Snd Expr
  | Inl Expr
  | Inr Expr
  | Bool Bool
  deriving (Eq, Show)

substExpr :: (Name, Expr) -> Expr -> Expr
substExpr arg@(name, newExpr) expr =
  case expr of
    Var name' ->
      if name == name' then newExpr else expr
    Ann e t -> Ann (substExpr arg e) t
    Lam x ty e ->
      if name == x then Lam x ty e else Lam x ty (substExpr arg e)
    App f x -> App (substExpr arg f) (substExpr arg x)
    LamTy x e -> LamTy x (substExpr arg e)
    AppTy e t -> AppTy (substExpr arg e) t
    Pack x t e -> Pack x t (substExpr arg e)
    Unpack (tyName, valueName, value) rest ->
      Unpack
        (tyName, valueName, substExpr arg value)
        (if name == valueName then rest else substExpr arg rest)
    U8 _ -> expr
    U16 _ -> expr
    U32 _ -> expr
    U64 _ -> expr
    Pair a b -> Pair (substExpr arg a) (substExpr arg b)
    Fst a -> Fst (substExpr arg a)
    Snd a -> Snd (substExpr arg a)
    Inl a -> Inl (substExpr arg a)
    Inr a -> Inr (substExpr arg a)
    Bool _ -> expr

elim :: Expr -> Expr -> Expr -> Expr
elim f g = App (App (App (Var (Name "elim")) f) g)

app :: Expr -> Expr -> Expr
app (Lam name _ body) x = substExpr (name, x) body
app (App (App (Var (Name "elim")) f) _) (Inl x) = app f x
app (App (App (Var (Name "elim")) _) g) (Inr x) = app g x
app f x = App f x

lam :: Name -> Ty -> Expr -> Expr
lam name _ (App f (Var name')) | name == name' = f
lam name ty body = Lam name ty body

lamTy :: Name -> Expr -> Expr
lamTy name (AppTy f (TVar name')) | name == name' = f
lamTy name body = LamTy name body

fst :: Expr -> Expr
fst (Pair a _) = a
fst a = Fst a

snd :: Expr -> Expr
snd (Pair _ b) = b
snd b = Snd b

pair :: Expr -> Expr -> Expr
pair (Fst a) (Snd a') | a == a' = a
pair a b = Pair a b

substTyExpr :: (Name, Ty) -> Expr -> Expr
substTyExpr arg@(name, _) expr =
  case expr of
    Var _ -> expr
    Ann e t -> Ann (substTyExpr arg e) (substTy arg t)
    Lam x ty e -> Lam x (substTy arg ty) (substTyExpr arg e)
    App f x -> App (substTyExpr arg f) (substTyExpr arg x)
    LamTy x e ->
      if name == x then LamTy x e else LamTy x (substTyExpr arg e)
    AppTy e t -> AppTy (substTyExpr arg e) (substTy arg t)
    Pack x t e ->
      Pack
        x
        (substTy arg t)
        (if name == x then e else substTyExpr arg e)
    Unpack (tyName, valueName, value) rest ->
      Unpack
        (tyName, valueName, substTyExpr arg value)
        (if name == tyName then rest else substTyExpr arg rest)
    U8 _ -> expr
    U16 _ -> expr
    U32 _ -> expr
    U64 _ -> expr
    Pair a b -> Pair (substTyExpr arg a) (substTyExpr arg b)
    Fst a -> Fst (substTyExpr arg a)
    Snd a -> Snd (substTyExpr arg a)
    Inl a -> Inl (substTyExpr arg a)
    Inr a -> Inr (substTyExpr arg a)
    Bool _ -> expr

appTy :: Expr -> Ty -> Expr
appTy (LamTy name body) t = substTyExpr (name, t) body
appTy e t = AppTy e t

castTo :: forall a. Num a => Integer -> Maybe a
castTo n =
  if fromIntegral (minBound @Word8) <= n
    && n <= fromIntegral (maxBound @Word8)
    then Just (fromIntegral @Integer @a n)
    else Nothing