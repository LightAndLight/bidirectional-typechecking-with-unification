module Print where

import Type (Ty (..))
import Core (Expr(..))
import Name (showName)

parens :: String -> String
parens a = "(" <> a <> ")"

showTy :: Ty -> String
showTy ty =
  case ty of
    TVar n -> showName n
    TUnknown n -> "?" <> show n
    TArrow a b ->
      ( case a of
          TArrow _ _ -> parens
          TForall _ _ -> parens
          _ -> id
      )
        (showTy a)
        <> " -> "
        <> showTy b
    TForall x t -> "forall " <> showName x <> ". " <> showTy t
    TExists x t -> "exists " <> showName x <> ". " <> showTy t
    TPair a b -> "(" <> showTy a <> ", " <> showTy b <> ")"
    TSum a b ->
      ( case a of
          TForall _ _ -> parens
          TExists _ _ -> parens
          _ -> id
      )
        (showTy a)
        <> " + "
        <> ( case b of
              TSum _ _ -> parens
              TForall _ _ -> parens
              TExists _ _ -> parens
              _ -> id
           )
          (showTy b)
    TU8 -> "u8"
    TU16 -> "u16"
    TU32 -> "u32"
    TU64 -> "u64"
    TBool -> "bool"

showExpr :: Expr -> String
showExpr expr =
  case expr of
    Var n -> showName n
    Ann e ty ->
      ( case e of
          Lam _ _ _ -> parens
          LamTy _ _ -> parens
          _ -> id
      )
        (showExpr e)
        <> " : "
        <> showTy ty
    Lam x mTy e ->
      case mTy of
        Nothing ->
          "\\" <> showName x <> " -> " <> showExpr e
        Just ty ->
          "\\(" <> showName x <> " : " <> showTy ty <> ") -> " <> showExpr e
    App f x ->
      ( case f of
          Lam _ _ _ -> parens
          LamTy _ _ -> parens
          _ -> id
      )
        (showExpr f)
        <> " "
        <> ( case x of
              Lam _ _ _ -> parens
              LamTy _ _ -> parens
              App _ _ -> parens
              Fst _ -> parens
              Snd _ -> parens
              Inl _ -> parens
              Inr _ -> parens
              _ -> id
           )
          (showExpr x)
    LamTy x e ->
      "forall " <> showName x <> ". " <> showExpr e
    AppTy e t ->
      ( case e of
          Lam _ _ _ -> parens
          LamTy _ _ -> parens
          _ -> id
      )
        (showExpr e)
        <> " @"
        <> ( case t of
              TArrow _ _ -> parens
              TForall _ _ -> parens
              TExists _ _ -> parens
              TSum _ _ -> parens
              _ -> id
           )
          (showTy t)
    Pack x ty e ->
      "exists " <> showName x <> ". ("
        <> showTy ty
        <> ", "
        <> showExpr e
        <> ")"
    Unpack (tyName, exprName, value) rest ->
      "unpack "
        <> "("
        <> showName tyName
        <> ", "
        <> showName exprName
        <> ") = "
        <> showExpr value
        <> " in "
        <> showExpr rest
    U8 n -> show n <> "_u8"
    U16 n -> show n <> "_u16"
    U32 n -> show n <> "_u32"
    U64 n -> show n <> "_u64"
    Pair a b ->
      "("
        <> showExpr a
        <> ", "
        <> showExpr b
        <> ")"
    Fst a ->
      "fst "
        <> showExpr a
    Snd a ->
      "snd "
        <> showExpr a
    Inl a ->
      "inl"
        <> "("
        <> showExpr a
        <> ")"
    Inr a ->
      "inr"
        <> "("
        <> showExpr a
        <> ")"
    Bool b ->
      if b then "true" else "false"