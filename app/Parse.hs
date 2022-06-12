{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Parse where

import Control.Applicative (many, optional, (<|>))
import Data.Char (isAlpha, isAlphaNum)
import Data.Word (Word8)
import Name (Name (..))
import Streaming.Chars (Chars)
import Syntax (Expr (..))
import Text.Parser.Char (char, satisfy, string)
import Text.Parser.Combinators (Parsing (unexpected))
import Text.Parser.Token (decimal, parens, symbol, symbolic)
import Text.Sage (Parser)
import Type (Ty (..))

name :: Chars s => Parser s Name
name = Name <$> ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum))

castTo :: forall a. Num a => Integer -> Maybe a
castTo n =
  if n < fromIntegral (maxBound @Word8)
    then Just (fromIntegral @Integer @a n)
    else Nothing

simpleExpr :: forall s. Chars s => Parser s Expr
simpleExpr =
  Var <$> name
    <|> intLiteral
    <|> parens (Pair <$> expr <* symbolic ',' <*> expr)
    <|> Bool True <$ symbol "true"
    <|> Bool False <$ symbol "false"
  where
    integerToExpr :: forall a. Num a => String -> (a -> Expr) -> Integer -> Parser s Expr
    integerToExpr size f x =
      maybe
        (unexpected $ show x <> " is out of the range of " <> size)
        (pure . f)
        (castTo @a x)

    intLiteral :: Parser s Expr
    intLiteral = do
      n <- decimal
      ( char '_'
          *> ( string "u8" *> integerToExpr "u8" U8 n
                <|> string "u16" *> integerToExpr "u16" U16 n
                <|> string "u32" *> integerToExpr "u32" U32 n
                <|> string "u64" *> integerToExpr "u64" U64 n
             )
        )
        <|> pure (Number n)

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
  -- e
  -- e : ty
  (\e -> maybe e (e `Ann`))
    <$> appExpr
      <*> optional (symbolic ':' *> type_)
    -- \x -> rest
    -- \(x : ty) -> rest
    <|> (\(arg, mTy) -> Lam arg mTy)
      <$ symbolic '\\'
      <*> ( (,) <$> name <*> pure Nothing
              <|> parens ((,) <$> name <* char ':' <*> fmap Just type_)
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

simpleType :: Chars s => Parser s Ty
simpleType =
  TVar <$> name
    <|> parens (TPair <$> type_ <* symbolic ',' <*> type_)
    <|> TU8 <$ symbol "u8"
    <|> TU16 <$ symbol "u16"
    <|> TU32 <$ symbol "u32"
    <|> TU64 <$ symbol "u64"
    <|> TBool <$ symbol "bool"

sumType :: Chars s => Parser s Ty
sumType = foldl TSum <$> simpleType <*> many simpleType

arrowType :: Chars s => Parser s Ty
arrowType =
  foldr TArrow <$> sumType <*> many (symbol "->" *> sumType)

type_ :: Chars s => Parser s Ty
type_ =
  TForall <$ symbol "forall" <*> name <* symbolic '.' <*> type_
    <|> TExists <$ symbol "exists" <*> name <* symbolic '.' <*> type_
    <|> arrowType