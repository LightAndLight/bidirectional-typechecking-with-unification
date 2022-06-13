{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Check
import Control.Applicative ((<**>))
import Data.Bitraversable (bitraverse)
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Options.Applicative as Options
import qualified Parse
import System.IO (stdin)
import Text.Parser.Combinators (eof)
import qualified Text.Sage as Sage

data Cli = Eval {cliInput :: ByteString}

cliParser :: Options.Parser Cli
cliParser =
  Options.subparser
    ( Options.command "eval" $
        Options.info
          ( Eval
              <$> Options.strArgument (Options.metavar "FILE")
          )
          Options.fullDesc
    )

main :: IO ()
main = do
  cli <- Options.execParser $ Options.info (cliParser <**> Options.helper) Options.fullDesc
  case cli of
    Eval input -> do
      input' <-
        case input of
          "-" -> ByteString.hGetContents stdin
          _ -> pure input
      expr <-
        case Sage.parseUtf8 (Parse.expr <* eof) input' of
          Left err -> error $ show err
          Right expr -> pure expr
      (expr', ty) <-
        case Check.runTC $ Check.infer [] expr >>= bitraverse Check.zonkExpr Check.zonkTy of
          Left err -> error $ show err
          Right res -> pure res
      _ expr' ty
