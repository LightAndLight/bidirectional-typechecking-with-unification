{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Parse where

import Control.Applicative (many, optional, (<|>))
import Data.Char (isAlpha, isAlphaNum)
import Name (Name (..))
import Streaming.Chars (Chars)
import Syntax (Expr (..))
import Text.Parser.Char (char, satisfy, string)
import Text.Parser.Token (decimal, parens, symbol, symbolic, token)
import Text.Sage (Parser)
import Type (Ty (..))

name :: Chars s => Parser s Name
name = token $ Name <$> ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum))

simpleExpr :: forall s. Chars s => Parser s Expr
simpleExpr =
  Var <$> name
    <|> intLiteral
    <|> parens ((\a -> maybe a (a `Pair`)) <$> expr <*> optional (symbolic ',' *> expr))
    <|> Bool True <$ symbol "true"
    <|> Bool False <$ symbol "false"
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