{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import Control.Monad
import Core (Expr (..))
import Data.Bifunctor
import Data.Bitraversable
import Name (Name (..))
import Type (Ty (..))
import Prelude hiding (fst, snd)
import Print (showExpr, showTy)
import Check (runTC, zonkExpr, check, zonkTy, infer)

main :: IO ()
main = do
  either print putStrLn . fmap showExpr . runTC $
    zonkExpr
      =<< check [] (Lam (Name "x") Nothing $ Var $ Name "x") (TArrow TU8 TU8)
  putStrLn ""

  either print putStrLn . fmap showExpr . runTC $
    zonkExpr
      =<< check [] (Lam (Name "x") Nothing $ Var $ Name "x") (TArrow TU8 TU32)
  putStrLn ""

  either print ((\(x, y) -> putStrLn x *> putStrLn y) . bimap showExpr showTy) . runTC $
    bitraverse zonkExpr zonkTy
      =<< infer
        []
        ( Lam
            (Name "f")
            (Just $ TArrow (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a")) TU8)
            $ Lam
              (Name "x")
              Nothing
              $ App (Var $ Name "f") (Var $ Name "x")
        )
  putStrLn ""

  either print ((\(x, y) -> putStrLn x *> putStrLn y) . bimap showExpr showTy) . runTC $
    bitraverse zonkExpr zonkTy
      =<< infer
        []
        ( Lam
            (Name "f")
            (Just $ TArrow (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a")) TU8)
            $ Lam
              (Name "x")
              Nothing
              $ Ann (App (Var $ Name "f") (Var $ Name "x")) TU16
        )
  putStrLn ""

  either print ((\(x, y) -> putStrLn x *> putStrLn y) . bimap showExpr showTy) . runTC $
    bitraverse zonkExpr zonkTy
      =<< infer
        []
        -- (\x -> \(f : (forall a. a -> a) -> u8) -> f x) (\y -> y)
        -- ~>
        -- (\x -> \(f : (forall a. a -> a) -> u8) -> f x) (forall a. \(y : a) -> y)
        ( ( Lam
              (Name "x")
              Nothing
              $ Lam
                (Name "f")
                (Just $ TArrow (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a")) TU8)
                $ Ann (App (Var $ Name "f") (Var $ Name "x")) TU16
          )
            `App` Lam (Name "y") Nothing (Var $ Name "y")
        )
  putStrLn ""

  either print ((\(x, y) -> putStrLn x *> putStrLn y) . bimap showExpr showTy) . runTC $
    bitraverse zonkExpr zonkTy
      =<< infer
        []
        -- (\(f : forall a. a -> a) -> f 99) (\y -> y)
        -- ~>
        -- (\(f : forall a. a -> a) -> f @u8 99_u8) (forall a. \(y : a) -> y)
        ( Lam
            (Name "f")
            (Just $ TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a"))
            (App (Var $ Name "f") (U8 99))
            `App` Lam (Name "y") Nothing (Var $ Name "y")
        )
  putStrLn ""

  either print ((\(x, y) -> putStrLn x *> putStrLn y) . bimap showExpr showTy) . runTC $
    bitraverse zonkExpr zonkTy
      =<< infer
        []
        -- \(f : forall a. a -> a) -> f 99
        -- ~>
        -- \(f : forall a. a -> a) -> f @u8 99_u8
        ( Lam
            (Name "f")
            (Just $ TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a"))
            (App (Var $ Name "f") (U8 99))
        )

  either print (putStrLn . showExpr) . runTC $
    zonkExpr
      =<< check
        []
        ( (Lam (Name "x") Nothing $ Snd $ Var (Name "x"))
            `App` Pair (U8 1) (U8 2)
        )
        TU16

  either print (putStrLn . showExpr) . runTC $
    zonkExpr
      =<< check
        []
        ( (Lam (Name "x") (Just $ TPair TU8 TU16) $ Snd $ Var (Name "x"))
            `App` Pair (U8 1) (U8 2)
        )
        TU16

  either print ((\(x, y) -> putStrLn x *> putStrLn y) . bimap showExpr showTy) . runTC $
    bitraverse zonkExpr zonkTy
      =<< infer
        []
        ( Lam (Name "x") (Just $ TSum TU8 TU16) $
            Var (Name "x") `Ann` TSum TU16 TU16
        )
