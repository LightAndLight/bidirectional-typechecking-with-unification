module Type where

import qualified Data.List as List
import Name (Name)

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
  deriving (Eq, Show)

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

allMetas :: Ty -> [Int]
allMetas ty =
  case ty of
    TVar _ -> []
    TUnknown meta -> [meta]
    TArrow a b -> allMetas a `List.union` allMetas b
    TForall _ t -> allMetas t
    TExists _ t -> allMetas t
    TPair a b -> allMetas a `List.union` allMetas b
    TSum a b -> allMetas a `List.union` allMetas b
    TU8 -> []
    TU16 -> []
    TU32 -> []
    TU64 -> []
    TBool -> []