{-# LANGUAGE DeriveGeneric #-}

module Name where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data Name
  = Name String
  | Fresh Int
  deriving (Eq, Show, Generic)

instance Hashable Name

showName :: Name -> String
showName name =
  case name of
    Name s -> s
    Fresh n -> "#" <> show n