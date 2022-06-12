{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}

module Check where

import Control.Monad (when)
import Core (Expr (..), app, appTy, castTo, fst, lam, lamTy, pair, snd)
import Data.Foldable (foldlM)
import Data.Word (Word16, Word32, Word64, Word8)
import Name (Name (..))
import qualified Syntax
import Type (Ty (..), hasVar, occursIn, substTy)
import Prelude hiding (fst, snd)

data Actual
  = Number
  | Ty Ty
  deriving (Eq, Show)

data Error
  = NotInScope Name
  | NotASubtypeOf Ty Actual
  | EscapedTyVar Name
  | Occurs Int Ty
  | Can'tInfer Syntax.Expr
  | OutOfBounds Integer Ty
  deriving (Eq, Show)

data State = State {stMetas :: Int, stFresh :: Int, stSolutions :: [(Int, Ty)]}

newtype TC a = TC (State -> Either Error (State, a))
  deriving (Functor)

runTC :: TC a -> Either Error a
runTC (TC m) = do
  (_, a) <- m (State 0 0 [])
  pure a

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
    TSum a b -> TSum <$> zonkTy a <*> zonkTy b
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
    Lam x ty e -> Lam x <$> zonkTy ty <*> zonkExpr e
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
    Inl e -> Inl <$> zonkExpr e
    Inr e -> Inr <$> zonkExpr e
    Bool _ -> pure expr

infer :: [(Name, Ty)] -> Syntax.Expr -> TC (Expr, Ty)
infer ctx expr =
  case expr of
    Syntax.Var (Name "elim") ->
      pure
        ( Var $ Name "elim"
        , TForall (Name "a") $
            TForall (Name "b") $
              TForall (Name "x") $
                TArrow (TArrow (TVar $ Name "a") (TVar $ Name "x")) $
                  TArrow (TArrow (TVar $ Name "b") (TVar $ Name "x")) $
                    TArrow (TSum (TVar $ Name "a") (TVar $ Name "b")) (TVar $ Name "x")
        )
    Syntax.Var x ->
      case lookup x ctx of
        Nothing -> typeError $ NotInScope x
        Just ty -> pure (Var x, ty)
    Syntax.Ann e t -> do
      e' <- check ctx e t
      pure (e', t)
    Syntax.Lam x mTy e -> do
      inTy <- case mTy of
        Nothing -> unknown
        Just ty -> pure ty
      (e', eTy) <- infer ((x, inTy) : ctx) e
      pure (Lam x inTy e', TArrow inTy eTy)
    Syntax.App f x -> do
      inTy <- unknown
      outTy <- unknown
      f' <- check ctx f (TArrow inTy outTy)
      x' <- check ctx x inTy
      pure (App f' x', outTy)
    Syntax.LamTy x e -> do
      (e', eTy) <- infer ctx e
      pure (LamTy x e', TForall x eTy)
    Syntax.AppTy e t -> do
      name <- freshName
      ty <- unknown
      e' <- check ctx e (TForall name ty)
      pure (AppTy e' t, ty)
    Syntax.Pack name ty e -> do
      (e', eTy) <- infer ctx e
      pure (Pack name ty e', TExists name eTy)
    Syntax.Unpack (tyName, varName, v) rest -> do
      name <- freshName
      ty <- unknown
      v' <- check ctx v (TExists name ty)
      (rest', restTy) <- infer ((varName, ty) : ctx) rest
      escaped <-
        foldlM
          ( \acc (_, varTy) -> do
              if acc
                then pure True
                else do
                  varTy' <- zonkTy varTy
                  pure $ hasVar tyName varTy'
          )
          False
          ctx
      when (escaped || hasVar tyName restTy) . typeError $ EscapedTyVar tyName
      pure (Unpack (tyName, varName, v') rest', restTy)
    Syntax.Number _ -> typeError $ Can'tInfer expr
    Syntax.Pair a b -> do
      (a', aTy) <- infer ctx a
      (b', bTy) <- infer ctx b
      pure (Pair a' b', TPair aTy bTy)
    Syntax.Fst e -> do
      a <- unknown
      b <- unknown
      e' <- check ctx e (TPair a b)
      pure (Fst e', a)
    Syntax.Snd e -> do
      a <- unknown
      b <- unknown
      e' <- check ctx e (TPair a b)
      pure (Snd e', b)
    Syntax.Inl a -> do
      (a', aTy) <- infer ctx a
      bTy <- unknown
      pure (Inl a', TSum aTy bTy)
    Syntax.Inr b -> do
      aTy <- unknown
      (b', bTy) <- infer ctx b
      pure (Inr b', TSum aTy bTy)
    Syntax.Bool b -> pure (Bool b, TBool)

walk :: Ty -> TC Ty
walk ty@(TUnknown u) = do
  uSol <- lookupMeta u
  case uSol of
    Nothing -> pure ty
    Just ty' -> walk ty'
walk ty = pure ty

subtypeOf :: [(Name, Ty)] -> (Expr, Ty) -> Ty -> TC Expr
subtypeOf ctx (expr, a) b = do
  a' <- walk a
  b' <- walk b
  subtypeOf' ctx (expr, a') b'

{- | @a `subtypeOf` b@ means that values of type @a@
 can be used when values of type @b@ are required.
-}
subtypeOf' :: [(Name, Ty)] -> (Expr, Ty) -> Ty -> TC Expr
-- infer generalisation for lambda abstractions
subtypeOf' ctx (expr@Lam{}, a) (TForall x t) = do
  -- When is an arbitrary @a@ a subtype of @forall x. t@?
  --
  -- When @a@ is a subtype of @t@ (generalisation)
  --
  -- All the metas that contain `x` as in their solution
  -- must occur exclusively in `a`.
  --
  -- In other words, throw an error if there are metas
  -- not reachable from `a` that contain `x` in their solution.
  a' <- subtypeOf ctx (expr, a) t
  escaped <-
    foldlM
      ( \acc (_, varTy) -> do
          if acc
            then pure True
            else hasVar x <$> zonkTy varTy
      )
      False
      ctx
  when escaped . typeError $ EscapedTyVar x
  pure $ lamTy x a'
subtypeOf' ctx (expr, TForall x t) b = do
  -- When is @forall x. t@ a subtype of some arbitrary @b@?
  --
  -- When @t[x := ?]@ is a subtype of @b@ (instantiation)
  ty <- unknown
  subtypeOf ctx (expr `appTy` ty, substTy (x, ty) t) b
subtypeOf' ctx (expr, a) (TExists x t) = do
  -- When is an arbitrary @a@ a subtype of @exists x. t@?
  --
  -- When @a@ is a subtype of @t[x := ?]@ (dual of instantiation)
  ty <- unknown
  expr' <- subtypeOf ctx (expr, a) (substTy (x, ty) t)
  pure $ Pack x ty expr'
subtypeOf' ctx (expr, a) b =
  case a of
    TVar v ->
      case b of
        TVar v' ->
          if v == v'
            then pure expr
            else typeError $ NotASubtypeOf a (Ty b)
        TUnknown u -> expr <$ solve u a
        _ ->
          typeError $ NotASubtypeOf a (Ty b)
    TUnknown u ->
      case b of
        TUnknown u' | u == u' -> pure expr
        _ -> expr <$ solve u b
    TArrow x y ->
      case b of
        TArrow x' y' -> do
          name <- freshName
          xExpr <- subtypeOf ctx (Var name, x') x
          yExpr <- subtypeOf ctx (expr `app` xExpr, y) y'
          pure $ lam name x yExpr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)
    TExists x t -> error "exists" x t
    TPair x y ->
      case b of
        TPair x' y' -> do
          xExpr <- subtypeOf ctx (fst expr, x) x'
          yExpr <- subtypeOf ctx (snd expr, y) y'
          pure $ pair xExpr yExpr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)
    TSum x y ->
      case b of
        TSum x' y' -> do
          lname <- freshName
          rname <- freshName
          xExpr <- subtypeOf ctx (Var lname, x) x'
          yExpr <- subtypeOf ctx (Var rname, y) y'
          pure $
            App
              ( App
                  ( App
                      (AppTy (AppTy (AppTy (Var $ Name "elim") x) y) (TSum x' y'))
                      (Lam lname x $ Inl xExpr)
                  )
                  (Lam rname y $ Inr yExpr)
              )
              expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)
    TU8 ->
      case b of
        TU8 -> pure expr
        TU16 -> pure $ Var (Name "u8_to_u16") `app` expr
        TU32 -> pure $ Var (Name "u8_to_u32") `app` expr
        TU64 -> pure $ Var (Name "u8_to_u64") `app` expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)
    TU16 ->
      case b of
        TU16 -> pure expr
        TU32 -> pure $ Var (Name "u16_to_u32") `app` expr
        TU64 -> pure $ Var (Name "u16_to_u64") `app` expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)
    TU32 ->
      case b of
        TU32 -> pure expr
        TU64 -> pure $ Var (Name "u32_to_u64") `app` expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)
    TU64 ->
      case b of
        TU64 -> pure expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)
    TBool ->
      case b of
        TBool -> pure expr
        TUnknown u -> expr <$ solve u a
        _ -> typeError $ NotASubtypeOf a (Ty b)

check :: [(Name, Ty)] -> Syntax.Expr -> Ty -> TC Expr
check _ expr@(Syntax.Number n) ty = do
  ty' <- zonkTy ty
  case ty' of
    TU8 ->
      maybe (typeError $ OutOfBounds n TU8) (pure . U8) (castTo @Word8 n)
    TU16 ->
      maybe (typeError $ OutOfBounds n TU16) (pure . U16) (castTo @Word16 n)
    TU32 ->
      maybe (typeError $ OutOfBounds n TU32) (pure . U32) (castTo @Word32 n)
    TU64 ->
      maybe (typeError $ OutOfBounds n TU64) (pure . U64) (castTo @Word64 n)
    TUnknown _ -> typeError $ Can'tInfer expr
    _ -> typeError $ NotASubtypeOf ty Number
check ctx expr ty = do
  (expr', ty') <- infer ctx expr
  subtypeOf ctx (expr', ty') ty