{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Core where

import Data.HashMap.Strict (HashMap)
import Data.Word (Word16, Word32, Word64, Word8)
import Name (Name (..))

data FieldTy
  = Optional Ty
  | Default Ty Expr
  | Required Ty
  deriving (Eq, Show)

data Ty
  = TVar Name
  | TUnknown Int
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
  | TOptional Ty
  deriving (Eq, Show)

substFieldTy :: (Name, Ty) -> FieldTy -> FieldTy
substFieldTy arg fieldTy =
  case fieldTy of
    Optional ty -> Optional (substTy arg ty)
    Required ty -> Required (substTy arg ty)
    Default ty expr -> Default (substTy arg ty) (substTyExpr arg expr)

substTy :: (Name, Ty) -> Ty -> Ty
substTy arg@(name, newTy) ty =
  case ty of
    TVar name' -> if name == name' then newTy else ty
    TUnknown _ -> ty
    TArrow a b -> TArrow (substTy arg a) (substTy arg b)
    TForall name' t -> TForall name' (substTy arg t)
    TExists name' t -> TExists name' (substTy arg t)
    TPair a b -> TPair (substTy arg a) (substTy arg b)
    TSum a b -> TSum (substTy arg a) (substTy arg b)
    TU8 -> ty
    TU16 -> ty
    TU32 -> ty
    TU64 -> ty
    TBool -> ty
    TRecord fields -> TRecord $ substFieldTy arg <$> fields
    TOptional a -> TOptional (substTy arg a)

exprHasTyVar :: Name -> Expr -> Bool
exprHasTyVar name expr =
  case expr of
    Var _ -> False
    Ann e ty -> exprHasTyVar name e || hasVar name ty
    Lam _ ty body -> hasVar name ty || exprHasTyVar name body
    App a b -> exprHasTyVar name a || exprHasTyVar name b
    LamTy name' body ->
      if name == name'
        then False
        else exprHasTyVar name body
    AppTy e ty -> exprHasTyVar name e || hasVar name ty
    Pack name' ty rest ->
      hasVar name ty
        || if name == name'
          then False
          else exprHasTyVar name rest
    Unpack (tyName, _exprName, value) rest ->
      exprHasTyVar name value
        || if name == tyName
          then False
          else exprHasTyVar name rest
    U8 _ -> False
    U16 _ -> False
    U32 _ -> False
    U64 _ -> False
    Pair a b -> exprHasTyVar name a || exprHasTyVar name b
    Fst a -> exprHasTyVar name a
    Snd a -> exprHasTyVar name a
    Inl a -> exprHasTyVar name a
    Inr a -> exprHasTyVar name a
    Bool _ -> False
    Record fields -> any (exprHasTyVar name) fields
    Project a _ -> exprHasTyVar name a
    None -> False
    Some a -> exprHasTyVar name a

fieldTyHasVar :: Name -> FieldTy -> Bool
fieldTyHasVar name fieldTy =
  case fieldTy of
    Optional ty -> hasVar name ty
    Required ty -> hasVar name ty
    Default ty expr -> hasVar name ty || exprHasTyVar name expr

hasVar :: Name -> Ty -> Bool
hasVar name ty =
  case ty of
    TVar name' -> name == name'
    TUnknown _ -> False
    TArrow a b -> hasVar name a || hasVar name b
    TForall name' t -> if name == name' then False else hasVar name t
    TExists name' t -> if name == name' then False else hasVar name t
    TPair a b -> hasVar name a || hasVar name b
    TSum a b -> hasVar name a || hasVar name b
    TU8 -> False
    TU16 -> False
    TU32 -> False
    TU64 -> False
    TBool -> False
    TRecord fields -> any (fieldTyHasVar name) fields
    TOptional a -> hasVar name a

occursInExpr :: Int -> Expr -> Bool
occursInExpr meta expr =
  case expr of
    Var _ -> False
    Ann e ty -> occursInExpr meta e || occursIn meta ty
    Lam _ ty body -> occursIn meta ty || occursInExpr meta body
    App a b -> occursInExpr meta a || occursInExpr meta b
    LamTy _ body ->
      occursInExpr meta body
    AppTy e ty -> occursInExpr meta e || occursIn meta ty
    Pack _ ty rest ->
      occursIn meta ty || occursInExpr meta rest
    Unpack (_, _, value) rest ->
      occursInExpr meta value || occursInExpr meta rest
    U8 _ -> False
    U16 _ -> False
    U32 _ -> False
    U64 _ -> False
    Pair a b -> occursInExpr meta a || occursInExpr meta b
    Fst a -> occursInExpr meta a
    Snd a -> occursInExpr meta a
    Inl a -> occursInExpr meta a
    Inr a -> occursInExpr meta a
    Bool _ -> False
    Record fields -> any (occursInExpr meta) fields
    Project a _ -> occursInExpr meta a
    None -> False
    Some a -> occursInExpr meta a

occursInFieldTy :: Int -> FieldTy -> Bool
occursInFieldTy meta fieldTy =
  case fieldTy of
    Optional ty -> occursIn meta ty
    Required ty -> occursIn meta ty
    Default ty expr -> occursIn meta ty || occursInExpr meta expr

occursIn :: Int -> Ty -> Bool
occursIn meta ty =
  case ty of
    TVar _ -> False
    TUnknown meta' -> meta == meta'
    TArrow a b -> occursIn meta a || occursIn meta b
    TForall _ t -> occursIn meta t
    TExists _ t -> occursIn meta t
    TPair a b -> occursIn meta a || occursIn meta b
    TSum a b -> occursIn meta a || occursIn meta b
    TU8 -> False
    TU16 -> False
    TU32 -> False
    TU64 -> False
    TBool -> False
    TRecord fields -> any (occursInFieldTy meta) fields
    TOptional a -> occursIn meta a

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
  | Record (HashMap String Expr)
  | Project Expr String
  | None
  | Some Expr
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
    Record fields -> Record (substExpr arg <$> fields)
    Project a field -> Project (substExpr arg a) field
    None -> expr
    Some a -> Some (substExpr arg a)

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
    Record fields -> Record (substTyExpr arg <$> fields)
    Project a field -> Project (substTyExpr arg a) field
    None -> expr
    Some a -> Some (substTyExpr arg a)

appTy :: Expr -> Ty -> Expr
appTy (LamTy name body) t = substTyExpr (name, t) body
appTy e t = AppTy e t

castTo :: forall a. Num a => Integer -> Maybe a
castTo n =
  if fromIntegral (minBound @Word8) <= n
    && n <= fromIntegral (maxBound @Word8)
    then Just (fromIntegral @Integer @a n)
    else Nothing