{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Parse where

import Control.Applicative (many, optional, (<|>))
import Data.Char (isAlpha, isAlphaNum)
import qualified Data.HashMap.Strict as HashMap
import Name (Name (..))
import Streaming.Chars (Chars)
import Syntax (Branch (..), Expr (..), FieldTy (..), Pattern (..), Ty (..))
import Text.Parser.Char (char, satisfy, string)
import Text.Parser.Combinators (sepBy)
import Text.Parser.Token (braces, comma, decimal, parens, semi, symbol, symbolic, token)
import Text.Sage (Parser)

ident :: Chars s => Parser s String
ident = token $ (:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)

name :: Chars s => Parser s Name
name = Name <$> ident

simpleExpr :: forall s. Chars s => Parser s Expr
simpleExpr =
  intLiteral
    <|> parens ((\a -> maybe a (a `Pair`)) <$> expr <*> optional (symbolic ',' *> expr))
    <|> braces (Record . HashMap.fromList <$> sepBy ((,) <$> ident <* symbolic '=' <*> expr) comma)
    <|> Bool True <$ symbol "true"
    <|> Bool False <$ symbol "false"
    <|> None <$ symbol "None"
    <|> Some <$ string "Some" <*> parens expr
    <|> Var <$> name
  where
    intLiteral :: Parser s Expr
    intLiteral =
      token $
        (\n -> maybe (Number n) ($ Number n))
          <$> decimal
          <*> optional
            ( char '_'
                *> ( (`Ann` TU8) <$ string "u8"
                       <|> (`Ann` TU16) <$ string "u16"
                       <|> (`Ann` TU32) <$ string "u32"
                       <|> (`Ann` TU64) <$ string "u64"
                   )
            )

mkApp :: Expr -> Expr -> Expr
mkApp (Var (Name "fst")) a = Fst a
mkApp (Var (Name "snd")) a = Snd a
mkApp (Var (Name "inl")) a = Inl a
mkApp (Var (Name "inr")) a = Inr a
mkApp a b = App a b

appExpr :: forall s. Chars s => Parser s Expr
appExpr =
  foldl mkApp <$> simpleExpr <*> many simpleExpr
    <|> foldl AppTy <$> simpleExpr <*> many simpleType

pattern :: Chars s => Parser s Pattern
pattern =
  PTrue <$ symbol "true"
    <|> PFalse <$ symbol "false"

branch :: Chars s => Parser s Branch
branch =
  Branch
    <$> pattern
    <* symbol "->"
    <*> expr

expr :: forall s. Chars s => Parser s Expr
expr =
  -- \x -> rest
  -- \(x : ty) -> rest
  (\(arg, mTy) -> Lam arg mTy)
    <$ symbolic '\\'
    <*> ( (,) <$> name <*> pure Nothing
            <|> parens ((,) <$> name <* symbolic ':' <*> fmap Just type_)
        )
    <* symbol "->"
    <*> expr
    -- forall x. rest
    <|> LamTy
      <$ symbol "forall"
      <*> name
      <* symbolic '.'
      <*> expr
    -- pack x = ty in rest
    <|> Pack
      <$ symbol "pack"
      <*> name
      <* symbolic '='
      <*> type_
      <* symbol "in"
      <*> expr
    -- let exists x. name = val in rest
    <|> Unpack
      <$ symbol "let"
      <* symbol "exists"
      <*> ((,,) <$> name <* symbolic '.' <*> name <* symbolic '=' <*> expr)
      <* symbol "in"
      <*> expr
    <|> Case
      <$ symbol "case"
      <*> expr
      <* symbol "of"
      <*> braces (branch `sepBy` semi)
    <|>
    -- e
    -- e : ty
    (\e -> maybe e (e `Ann`))
      <$> appExpr
      <*> optional (symbolic ':' *> type_)

simpleType :: Chars s => Parser s Ty
simpleType =
  parens type_
    <|> TU8 <$ symbol "u8"
    <|> TU16 <$ symbol "u16"
    <|> TU32 <$ symbol "u32"
    <|> TU64 <$ symbol "u64"
    <|> TBool <$ symbol "bool"
    <|> TVar <$> name
    <|> braces
      ( TRecord . HashMap.fromList
          <$> sepBy
            ( do
                field <- ident
                isOptional <- True <$ symbolic '?' <|> pure False
                if isOptional
                  then (,) field . Optional <$ symbolic ':' <*> type_
                  else
                    (\ty -> maybe (field, Required ty) ((,) field . Default ty))
                      <$ symbolic ':'
                      <*> type_
                      <*> optional (symbolic '=' *> expr)
            )
            comma
      )

productType :: Chars s => Parser s Ty
productType = foldl TPair <$> simpleType <*> many (symbolic '*' *> simpleType)

sumType :: Chars s => Parser s Ty
sumType = foldl TSum <$> productType <*> many (symbolic '+' *> productType)

arrowType :: Chars s => Parser s Ty
arrowType =
  (\a -> maybe a (TArrow a))
    <$> sumType
    <*> optional (symbol "->" *> arrowType)

type_ :: Chars s => Parser s Ty
type_ =
  TForall <$ symbol "forall" <*> name <* symbolic '.' <*> type_
    <|> TExists <$ symbol "exists" <*> name <* symbolic '.' <*> type_
    <|> arrowType