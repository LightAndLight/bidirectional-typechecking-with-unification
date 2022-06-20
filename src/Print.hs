module Print where

import Core (Branch, Expr (..), FieldTy (..), Ty (..))
import Data.Function ((&))
import qualified Data.HashMap.Strict as HashMap
import Data.List (intercalate)
import Lens.Micro (mapped, (<>~), _last)
import Name (showName)

parens :: [String] -> [String]
parens a =
  case a of
    [] -> ["()"]
    [a'] -> ["(" <> a' <> ")"]
    _ ->
      ["("] <> a <> [")"]

oneLine :: [String] -> Maybe String
oneLine [] = Nothing
oneLine [x] = Just x
oneLine (_ : _ : _) = Nothing

indent :: Int -> [String] -> [String]
indent n as = (replicate n ' ' <>) <$> as

showFieldTy :: String -> FieldTy -> [String]
showFieldTy name fieldTy =
  case fieldTy of
    Required ty ->
      let ty' = showTy ty
          field = name <> " :"
       in case oneLine ty' of
            Nothing -> field : indent 2 ty'
            Just ty'' -> [field <> " " <> ty'']
    Optional ty ->
      let ty' = showTy ty
          field = name <> "? :"
       in case oneLine ty' of
            Nothing -> field : indent 2 ty'
            Just ty'' -> [field <> " " <> ty'']
    Default ty expr ->
      let ty' = showTy ty
          expr' = showExpr expr
          field = name <> " :"
          fieldAndTy = case oneLine ty' of
            Nothing -> field : ty'
            Just ty'' -> [field <> " " <> ty'']
       in case oneLine expr' of
            Nothing -> (fieldAndTy & _last <>~ " =") <> indent 2 expr'
            Just expr'' -> fieldAndTy & _last <>~ (" = " <> expr'')

showTy :: Ty -> [String]
showTy ty =
  case ty of
    TVar n -> [showName n]
    TUnknown n -> ["?" <> show n]
    TArrow a b ->
      let a' =
            ( case a of
                TArrow _ _ -> parens
                TForall _ _ -> parens
                _ -> id
            )
              (showTy a)
       in (a' & _last <>~ "->")
            <> showTy b
    TForall x t ->
      let t' = showTy t
          q = ["forall " <> showName x <> "."]
       in case oneLine t' of
            Nothing -> q <> t'
            Just t'' -> q & _last <>~ (" " <> t'')
    TExists x t ->
      let t' = showTy t
          q = ["exists " <> showName x <> "."]
       in case oneLine t' of
            Nothing -> q <> t'
            Just t'' -> q & _last <>~ (" " <> t'')
    TPair a b ->
      let a' =
            ( case a of
                TForall _ _ -> parens
                TExists _ _ -> parens
                TSum _ _ -> parens
                _ -> id
            )
              (showTy a)
          b' =
            ( case b of
                TPair _ _ -> parens
                TForall _ _ -> parens
                TExists _ _ -> parens
                TSum _ _ -> parens
                _ -> id
            )
              (showTy b)
          a'' = (a' & _last <>~ " *")
       in case oneLine b' of
            Nothing -> a'' <> b'
            Just b'' -> a'' & _last <>~ b''
    TSum a b ->
      let a' =
            ( case a of
                TForall _ _ -> parens
                TExists _ _ -> parens
                _ -> id
            )
              (showTy a)
          b' =
            ( case b of
                TSum _ _ -> parens
                TForall _ _ -> parens
                TExists _ _ -> parens
                _ -> id
            )
              (showTy b)
          a'' = (a' & _last <>~ " +")
       in case oneLine b' of
            Nothing -> a'' <> b'
            Just b'' -> a'' & _last <>~ b''
    TU8 -> ["u8"]
    TU16 -> ["u16"]
    TU32 -> ["u32"]
    TU64 -> ["u64"]
    TBool -> ["bool"]
    TRecord fields ->
      if HashMap.null fields
        then ["{}"]
        else
          let fields' :: [[String]]
              fields' = uncurry showFieldTy <$> HashMap.toList fields
           in case traverse oneLine fields' of
                Nothing -> ["{"] <> concat (fields' & mapped . _last <>~ ",") <> ["}"]
                Just fields'' -> ["{ " <> intercalate ", " fields'' <> " }"]
    TOptional a ->
      let a' = showTy a
       in case oneLine a' of
            Nothing -> ["Optional"] <> indent 2 a'
            Just a'' -> ["Optional " <> a'']

showBranch :: Branch -> [String]
showBranch = _

showExpr :: Expr -> [String]
showExpr expr =
  case expr of
    Var n -> [showName n]
    Ann e ty ->
      [ ( case e of
            Lam _ _ _ -> parens
            LamTy _ _ -> parens
            _ -> id
        )
          (showExpr e)
          <> " : "
          <> showTy ty
      ]
    Lam x ty e ->
      let e' = showExpr e
          lam = "\\(" <> showName x <> " : " <> showTy ty <> ") ->"
       in case e' of
            [] -> undefined
            [e''] ->
              [lam <> " " <> e']
            _ ->
              ["\\(" <> showName x <> " : " <> showTy ty <> ") ->"]
                <> e'
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
      "exists "
        <> showName x
        <> ". ("
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
    Record fields ->
      if HashMap.null fields
        then "{}"
        else "{ " <> intercalate ", " ((\(name, value) -> name <> " = " <> showExpr value) <$> HashMap.toList fields) <> " }"
    Project a field ->
      ( case a of
          App _ _ -> parens
          AppTy _ _ -> parens
          Lam _ _ _ -> parens
          LamTy _ _ -> parens
          _ -> id
      )
        (showExpr a)
        <> "."
        <> field
    None -> "None"
    Some a -> "Some(" <> showExpr a <> ")"
    Case a bs ->
      ["case " <> showExpr a <> " of {"]
        <> (fmap ("  " <>) . showBranch)
        =<< bs
          <> ["}"]