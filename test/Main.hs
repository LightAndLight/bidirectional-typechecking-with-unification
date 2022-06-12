{-# LANGUAGE OverloadedStrings #-}

module Main where

import Check (check, infer, runTC, zonkExpr, zonkTy)
import Core (Expr (..))
import Data.Bitraversable (bitraverse)
import Data.Text (Text)
import Name (Name (..))
import qualified Parse
import qualified Syntax
import Test.Hspec (describe, hspec, it, shouldBe)
import Text.Sage (parseText)
import Type (Ty (..))

parse :: Text -> IO Syntax.Expr
parse input =
  case parseText Parse.expr input of
    Left err -> error $ show err
    Right expr -> pure expr

main :: IO ()
main =
  hspec $ do
    describe "checking" $ do
      it "\\x -> x is checked by u8 -> u8" $ do
        let input = "\\x -> x"
        expr <- parse input
        runTC (check [] expr (TArrow TU8 TU8) >>= zonkExpr)
          `shouldBe` Right (Lam (Fresh 0) TU8 . Var $ Fresh 0)

      it "\\x -> x is checked by u8 -> u32" $ do
        let input = "\\x -> x"
        expr <- parse input
        runTC (check [] expr (TArrow TU8 TU32) >>= zonkExpr)
          `shouldBe` Right (Var $ Name "u8_to_u32")

      it "\\(f : forall a. a -> a) -> \\x -> f x infers (forall a. a -> a) -> ?2 -> ?2" $ do
        let input = "\\(f : forall a. a -> a) -> \\x -> f x"
        expr <- parse input
        runTC (infer [] expr >>= bitraverse zonkExpr zonkTy)
          `shouldBe` Right
            ( Lam (Name "f") (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a")) $
                Lam (Name "x") (TUnknown 2) $
                  App (AppTy (Var $ Name "f") (TUnknown 2)) (Var $ Name "x")
            , TArrow
                (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a"))
                $ TArrow (TUnknown 2) (TUnknown 2)
            )

      describe "\\(f : (forall a. a -> a) -> u8) -> \\x -> f x : u16 infers ((forall a. a -> a) -> u8) -> (forall a. a -> a) -> u16" $ do
        let input = "\\(f : (forall a. a -> a) -> u8) -> \\x -> f x : u16"
        it "parses" $ do
          case parseText Parse.expr input of
            Left err -> error $ show err
            Right expr ->
              expr
                `shouldBe` Syntax.Lam
                  (Name "f")
                  (Just $ TArrow (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) TU8)
                  ( Syntax.Lam (Name "x") Nothing $
                      Syntax.App (Syntax.Var $ Name "f") (Syntax.Var $ Name "x") `Syntax.Ann` TU16
                  )
        it "checks" $ do
          expr <- parse input
          runTC (infer [] expr >>= bitraverse zonkExpr zonkTy)
            `shouldBe` Right
              ( Lam (Name "f") (TArrow (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) TU8) $
                  Lam (Name "x") (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) $
                    App (Var $ Name "u8_to_u16") (App (Var $ Name "f") (Var $ Name "x"))
              , TArrow (TArrow (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) TU8) $
                  TArrow (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) TU16
              )

      it "(\\x -> \\(f : (forall a. a -> a) -> u8) -> f x : u16) (\\y -> y) infers ((forall a. a -> a) -> u8) -> u16" $ do
        let input = "(\\x -> \\(f : (forall a. a -> a) -> u8) -> f x : u16) (\\y -> y)"
        expr <- parse input
        runTC (infer [] expr >>= bitraverse zonkExpr zonkTy)
          `shouldBe` Right
            ( App
                ( Lam (Fresh 1) (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) $
                    Lam (Name "f") (TArrow (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) TU8) $
                      App (Var $ Name "u8_to_u16") (App (Var $ Name "f") (Var $ Fresh 1))
                )
                ( LamTy (Name "a") $
                    Lam (Fresh 2) (TVar $ Name "a") $
                      Var (Fresh 2)
                )
            , TArrow (TArrow (TForall (Name "a") (TArrow (TVar $ Name "a") (TVar $ Name "a"))) TU8) TU16
            )

      it "\\(f : forall a. a -> a) -> f (99 : u8) infers (forall a. a -> a) -> u8" $ do
        let input = "\\(f : forall a. a -> a) -> f (99 : u8)"
        expr <- parse input
        runTC (infer [] expr >>= bitraverse zonkExpr zonkTy)
          `shouldBe` Right
            ( Lam (Name "f") (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a")) $
                App (AppTy (Var $ Name "f") TU8) (U8 99)
            , TArrow
                (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a"))
                TU8
            )

      it "(\\(f : forall a. a -> a) -> f (99 : u8)) (\\y -> y) infers u8" $ do
        let input = "(\\(f : forall a. a -> a) -> f (99 : u8)) (\\y -> y)"
        expr <- parse input
        runTC (infer [] expr >>= bitraverse zonkExpr zonkTy)
          `shouldBe` Right
            ( App
                ( Lam (Fresh 1) (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a")) $
                    App (AppTy (Var $ Fresh 1) TU8) (U8 99)
                )
                (LamTy (Name "a") $ Lam (Fresh 2) (TVar $ Name "a") $ Var (Fresh 2))
            , TU8
            )

      it "(\\x -> snd x) (1_u8, 2_u8) is checked by u16" $ do
        let input = "(\\x -> snd x) (1_u8, 2_u8)"
        expr <- parse input
        runTC (check [] expr TU16 >>= zonkExpr)
          `shouldBe` Right
            ( App
                (Var $ Name "u8_to_u16")
                ( App
                    (Lam (Fresh 0) (TPair TU8 TU8) $ Snd (Var $ Fresh 0))
                    (Pair (U8 1) (U8 2))
                )
            )

      it "(\\x -> snd x) (1_u8, 2_u16) is checked by u16" $ do
        let input = "(\\x -> snd x) (1_u8, 2_u16)"
        expr <- parse input
        runTC (check [] expr TU16 >>= zonkExpr)
          `shouldBe` Right
            ( App
                (Lam (Fresh 0) (TPair TU8 TU16) $ Snd (Var $ Fresh 0))
                (Pair (U8 1) (U16 2))
            )

      it "\\(x : u8 + u16) -> (x : u16 + u16)" $ do
        let input = "\\(x : u8 + u16) -> (x : u16 + u16)"
        expr <- parse input
        runTC (infer [] expr >>= bitraverse zonkExpr zonkTy)
          `shouldBe` Right
            ( Lam (Name "x") (TSum TU8 TU16) $
                App
                  ( App
                      ( App
                          (AppTy (AppTy (AppTy (Var $ Name "elim") TU8) TU16) (TSum TU16 TU16))
                          (Lam (Fresh 0) TU8 $ Inl (App (Var $ Name "u8_to_u16") (Var $ Fresh 0)))
                      )
                      (Lam (Fresh 1) TU16 $ Inr (Var $ Fresh 1))
                  )
                  (Var $ Name "x")
            , TArrow (TSum TU8 TU16) (TSum TU16 TU16)
            )