module Name where

data Name
  = Name String
  | Fresh Int
  deriving (Eq, Show)

showName :: Name -> String
showName name =
  case name of
    Name s -> s
    Fresh n -> "#" <> show n