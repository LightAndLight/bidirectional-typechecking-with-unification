{-# language DeriveFunctor #-}
{-# options_ghc -Wall -Werror #-}
module Main where

import Control.Monad
import Data.Word

data Ty
  = TVar Name
  | TUnknown Int
 
  | TArrow Ty Ty
 
  | TForall Name Ty
  | TExists Name Ty

  | TPair Ty Ty

  | TU8
  | TU16
  | TU32
  | TU64
 
  | TBool
  deriving (Eq, Show)

subst :: (Name, Ty) -> Ty -> Ty
subst arg@(name, newTy) ty =
  case ty of
    TVar name' -> if name == name' then newTy else ty
    TUnknown _ -> ty
    TArrow a b -> TArrow (subst arg a) (subst arg b)
    TForall name' t -> TForall name' (subst arg t)
    TExists name' t -> TExists name' (subst arg t)
    TPair a b -> TPair (subst arg a) (subst arg b)
    TU8 -> ty
    TU16 -> ty
    TU32 -> ty
    TU64 -> ty
    TBool -> ty

hasVar :: Name -> Ty -> Bool
hasVar name ty =
  case ty of
    TVar name' -> name == name'
    TUnknown _ -> False
    TArrow a b -> hasVar name a || hasVar name b
    TForall name' t -> if name == name' then False else hasVar name t
    TExists name' t -> if name == name' then False else hasVar name t
    TPair a b -> hasVar name a || hasVar name b
    TU8 -> False
    TU16 -> False
    TU32 -> False
    TU64 -> False
    TBool -> False

occursIn :: Int -> Ty -> Bool
occursIn meta ty =
  case ty of
    TVar _ -> False
    TUnknown meta' -> meta == meta'
    TArrow a b -> occursIn meta a || occursIn meta b
    TForall _ t -> occursIn meta t
    TExists _ t -> occursIn meta t
    TPair a b -> occursIn meta a || occursIn meta b
    TU8 -> False
    TU16 -> False
    TU32 -> False
    TU64 -> False
    TBool -> False

data Name
  = Name String
  | Fresh Int
  deriving (Eq, Show)

showName :: Name -> String
showName name =
  case name of
    Name s -> s
    Fresh n -> "#" <> show n

data Expr
  = Var Name

  | Ann Expr Ty
 
  | Lam Name (Maybe Ty) Expr
  | App Expr Expr

  | LamTy Name Expr
  | AppTy Expr Ty

  | Pack Name Ty Expr
  | Unpack (Name, Name, Expr) Expr

  | U8 Word8
  | U16 Word16
  | U32 Word32
  | U64 Word64

  | Pair Expr Expr
  | Fst Expr
  | Snd Expr
 
  | Bool Bool
  deriving (Eq, Show)

data Error
  = NotInScope Name
  | NotASubtypeOf Ty Ty
  | EscapedTyVar Name
  | Occurs Int Ty
  deriving (Eq, Show)

data State = State { stMetas :: Int, stFresh :: Int, stSolutions :: [(Int, Ty)] }

newtype TC a = TC (State -> Either Error (State, a))
  deriving Functor

runTC :: TC a -> Either Error a
runTC (TC m) = snd <$> m (State 0 0 [])

instance Applicative TC where
  pure a = TC $ \n -> pure (n, a)
  TC mf <*> TC mx =
    TC $ \n -> do
      (n', f) <- mf n
      (n'', x) <- mx n'
      pure (n'', f x)

instance Monad TC where
  TC ma >>= f =
    TC $ \n -> do
      (n', a) <- ma n
      let TC mb = f a
      mb n'

unknown :: TC Ty
unknown = 
  TC $ \(State metas freshs solutions) ->
  pure (State (metas + 1) freshs solutions, TUnknown metas)

freshName :: TC Name
freshName =
  TC $ \(State metas freshs solutions) ->
  pure (State metas (freshs + 1) solutions, Fresh freshs)

typeError :: Error -> TC a
typeError err = TC $ \_ -> Left err

lookupMeta :: Int -> TC (Maybe Ty)
lookupMeta n =
  TC $ \st@(State _ _ solutions) -> pure (st, lookup n solutions)

solve :: Int -> Ty -> TC ()
solve n ty = do
  when (n `occursIn` ty) . typeError $ Occurs n ty
  mSol <- lookupMeta n
  case mSol of
    Nothing ->
      TC $ \(State metas freshs solutions) -> 
      pure (State metas freshs ((n, ty) : solutions), ())
    Just sol ->
      error "already solved" sol

zonkTy :: Ty -> TC Ty
zonkTy ty =
  case ty of
    TVar _ -> pure ty
    TUnknown m -> do
      mTy <- lookupMeta m
      case mTy of
        Nothing -> pure ty
        Just ty' -> zonkTy ty'
    TArrow a b -> TArrow <$> zonkTy a <*> zonkTy b
    TForall x t -> TForall x <$> zonkTy t
    TExists x t -> TExists x <$> zonkTy t
    TPair a b -> TPair <$> zonkTy a <*> zonkTy b
    TU8 -> pure ty
    TU16 -> pure ty
    TU32 -> pure ty
    TU64 -> pure ty
    TBool -> pure ty
 
zonkExpr :: Expr -> TC Expr
zonkExpr expr =
  case expr of
    Var _ -> pure expr
    Ann e ty -> Ann <$> zonkExpr e <*> zonkTy ty
    Lam x ty e -> Lam x <$> traverse zonkTy ty <*> zonkExpr e
    App f x -> App <$> zonkExpr f <*> zonkExpr x
    LamTy x e -> LamTy x <$> zonkExpr e
    AppTy e t -> AppTy <$> zonkExpr e <*> zonkTy t
    Pack x t e -> Pack x <$> zonkTy t <*> zonkExpr e
    Unpack (a, b, v) e ->
      Unpack <$> ((,,) a b <$> zonkExpr v) <*> zonkExpr e
    U8 _ -> pure expr
    U16 _ -> pure expr
    U32 _ -> pure expr
    U64 _ -> pure expr
    Pair a b -> Pair <$> zonkExpr a <*> zonkExpr b
    Fst e -> Fst <$> zonkExpr e
    Snd e -> Snd <$> zonkExpr e
    Bool _ -> pure expr

infer :: [(Name, Ty)] -> Expr -> TC (Expr, Ty)
infer ctx expr =
  case expr of
    Var x ->
      case lookup x ctx of
        Nothing -> typeError $ NotInScope x
        Just ty -> pure (expr, ty)

    Ann e t -> do
      e' <- check ctx e t
      pure (e', t)

    Lam x mTy e -> do
      inTy <- case mTy of
        Nothing -> unknown
        Just ty -> pure ty
      (e', eTy) <- infer ((x, inTy) : ctx) e
      pure (Lam x (Just inTy) e', TArrow inTy eTy)
    App f x -> do
      inTy <- unknown
      outTy <- unknown
      f' <- check ctx f (TArrow inTy outTy)
      x' <- check ctx x inTy
      pure (App f' x', outTy)

    LamTy x e -> do
      (e', eTy) <- infer ctx e
      pure (LamTy x e', TForall x eTy)
    AppTy e t -> do
      name <- freshName
      ty <- unknown
      e' <- check ctx e (TForall name ty)
      pure (AppTy e' t, ty)

    Pack name ty e -> do
      (e', eTy) <- infer ctx e
      pure (Pack name ty e', TExists name eTy)
    Unpack (tyName, varName, v) rest -> do
      name <- freshName
      ty <- unknown
      v' <- check ctx v (TExists name ty)
      (rest', restTy) <- infer ((varName, ty) : ctx) rest
      when (hasVar tyName restTy) . typeError $ EscapedTyVar tyName
      pure (Unpack (tyName, varName, v') rest', restTy)

    U8 _ -> pure (expr, TU8)
    U16 _ -> pure (expr, TU16)
    U32 _ -> pure (expr, TU32)
    U64 _ -> pure (expr, TU64)

    Pair a b -> do
      (a', aTy) <- infer ctx a
      (b', bTy) <- infer ctx b
      pure (Pair a' b', TPair aTy bTy)
    Fst e -> do
      a <- unknown
      b <- unknown
      e' <- check ctx e (TPair a b)
      pure (Fst e', a)
    Snd e -> do
      a <- unknown
      b <- unknown
      e' <- check ctx e (TPair a b)
      pure (Snd e', b)

    Bool _ -> pure (expr, TBool)

walk :: Ty -> TC Ty
walk ty@(TUnknown u) = do
  uSol <- lookupMeta u
  case uSol of
    Nothing -> pure ty
    Just ty' -> walk ty'
walk ty = pure ty

subtypeOf :: (Expr, Ty) -> Ty -> TC Expr
subtypeOf (expr, a) b = do
  a' <- walk a
  b' <- walk b
  subtypeOf' (expr, a') b'

-- | @a `subtypeOf` b@ means that values of type @a@
-- can be used when values of type @b@ are required.
subtypeOf' :: (Expr, Ty) -> Ty -> TC Expr

subtypeOf' (expr, TForall x t) (TForall x' t') =
  error "two foralls" expr x t x' t'
subtypeOf' (expr, a) (TForall x t) = do
  -- When is an arbitrary @a@ a subtype of @forall x. t@?
  --
  -- When @a@ is a subtype of @t@ (generalisation)
  LamTy x <$> subtypeOf (expr, a) t
subtypeOf' (expr, TForall x t) b = do
  -- When is @forall x. t@ a subtype of some arbitrary @b@?
  --
  -- When @t[x := ?]@ is a subtype of @b@ (instantiation)
  ty <- unknown
  subtypeOf (AppTy expr ty, subst (x, ty) t) b

subtypeOf' (expr, TExists x t) (TExists x' t') = do
  error "two exists" expr x t x' t'
subtypeOf' (expr, TExists x t) b = do
  -- When is @exists x. t@ a subtype of an arbitrary @b@?
  exprName <- freshName
  expr' <- subtypeOf (Var exprName, t) b
  pure $ Unpack (x, exprName, expr) expr'
subtypeOf' (expr, a) (TExists x t) = do
  -- When is an arbitrary @a@ a subtype of @exists x. t@?
  --
  -- When @a@ is a subtype of @t[x := ?]@
  ty <- unknown
  expr' <- subtypeOf (expr, a) (subst (x, ty) t)
  pure $ Pack x ty expr'

subtypeOf' (expr, a) b =
  case a of
    TVar v ->
      case b of
        TVar v' ->
          if v == v'
          then pure expr
          else typeError $ NotASubtypeOf a b
        TUnknown u -> expr <$ solve u a
        _ ->
          typeError $ NotASubtypeOf a b
    TUnknown u ->
      case b of
        TUnknown u' | u == u' -> pure expr
        _ -> expr <$ solve u b
    TArrow x y ->
      case b of
        TArrow x' y' -> do
          name <- freshName
          xExpr <- subtypeOf (Var name, x') x
          yExpr <- subtypeOf (App expr xExpr, y) y'
          pure $ Lam name (Just x) yExpr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a b
    TForall x t -> error "covered" x t
    TExists x t -> error "covered" x t
    TPair x y ->
      case b of
        TPair x' y' -> do
          xExpr <- subtypeOf (Fst expr, x) x'
          yExpr <- subtypeOf (Snd expr, y) y'
          pure $ Pair xExpr yExpr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a b
    TU8 ->
      case b of
        TU8 -> pure expr
        TU16 -> pure $ Var (Name "u8_to_u16") `App` expr
        TU32 -> pure $ Var (Name "u8_to_u32") `App` expr
        TU64 -> pure $ Var (Name "u8_to_u64") `App` expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a b
    TU16 ->
      case b of
        TU16 -> pure expr
        TU32 -> pure $ Var (Name "u16_to_u32") `App` expr
        TU64 -> pure $ Var (Name "u16_to_u64") `App` expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a b
    TU32 ->
      case b of
        TU32 -> pure expr
        TU64 -> pure $ Var (Name "u32_to_u64") `App` expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a b
    TU64 ->
      case b of
        TU64 -> pure expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a b
    TBool ->
      case b of
        TBool -> pure expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a b

check :: [(Name, Ty)] -> Expr -> Ty -> TC Expr
check ctx expr ty = do
  (expr', ty') <- infer ctx expr
  subtypeOf (expr', ty') ty

parens :: String -> String
parens a = "(" <> a <> ")"

showTy :: Ty -> String
showTy ty =
  case ty of
    TVar n -> showName n
    TUnknown n -> "?" <> show n
    TArrow a b ->
      (case a of
        TArrow _ _ -> parens
        _ -> id)
      (showTy a) <>
      " -> " <>
      showTy b
    TForall x t -> "forall " <> showName x <> ". " <> showTy t
    TExists x t -> "exists " <> showName x <> ". " <> showTy t
    TPair a b -> "(" <> showTy a <> ", " <> showTy b <> ")"
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
      (case e of
        Lam _ _ _ -> parens
        LamTy _ _ -> parens
        _ -> id)
      (showExpr e) <> 
      " : " <> 
      showTy ty
    Lam x mTy e -> 
      case mTy of
        Nothing ->
          "\\" <> showName x <> " -> " <> showExpr e
        Just ty ->
          "\\(" <> showName x <> " : " <> showTy ty <> ") -> " <> showExpr e
    App f x -> 
      (case f of
        Lam _ _ _ -> parens
        LamTy _ _ -> parens
        _ -> id)
      (showExpr f) <> 
      " " <> 
      (case x of
        App _ _ -> parens
        Fst _ -> parens
        Snd _ -> parens
        _ -> id)
      (showExpr x)
    LamTy x e ->
      "forall " <> showName x <> ". " <> showExpr e
    AppTy e t ->
      (case e of 
        Lam _ _ _ -> parens
        LamTy _ _ -> parens
        _ -> id)
      (showExpr e) <> 
      " @" <> 
      (case t of
        TArrow _ _ -> parens
        _ -> id)
      (showTy t)
    Pack x ty e ->
      "exists " <> showName x <> ". (" <>
      showTy ty <>
      ", " <>
      showExpr e <>
      ")"
    Unpack (tyName, exprName, value) rest ->
      "unpack " <>
      "(" <> showName tyName <> ", " <> showName exprName <> ") = " <>
      showExpr value <>
      " in " <>
      showExpr rest
    U8 n -> show n <> "_u8"
    U16 n -> show n <> "_u16"
    U32 n -> show n <> "_u32"
    U64 n -> show n <> "_u64"
    Pair a b ->
      "(" <>
      showExpr a <>
      "," <>
      showExpr b <>
      ")"
    Fst a ->
      "fst " <>
      showExpr a
    Snd a ->
      "snd " <>
      showExpr a
    Bool b ->
      if b then "true" else "false"

main :: IO ()
main = do
  either print putStrLn . fmap showExpr . runTC $ 
    zonkExpr =<<
    check [] (Lam (Name "x") Nothing $ Var $ Name "x") (TArrow TU8 TU8)
  
  either print putStrLn . fmap showExpr . runTC $ 
    zonkExpr =<<
    check [] (Lam (Name "x") Nothing $ Var $ Name "x") (TArrow TU8 TU32)
  
  either print putStrLn . fmap showExpr . runTC $ 
    zonkExpr =<<
    check [] (Lam (Name "x") Nothing $ Var $ Name "x") (TForall (Name "a") $ TArrow (TVar $ Name "a") (TVar $ Name "a"))
