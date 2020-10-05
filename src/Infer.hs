{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
module Infer where

import qualified Data.Map                      as M
import qualified Data.Set                      as S
import           Control.Monad.Except
import           Control.Monad.State
import           Grammar
import           AST
import           Data.Foldable                  ( foldrM
                                                , foldlM
                                                )


newtype TVar = TV String
  deriving (Show, Eq, Ord)

data Type
  = TVar TVar
  | TCon TCon
  | TArr Type Type
  deriving (Show, Eq, Ord)

data TCon
  = CString
  | CNum
  | CBool
  deriving (Show, Eq, Ord)

infixr `TArr`

data Scheme = Forall [TVar] Type
  deriving (Show, Eq, Ord)

-- TODO: Convert back to a simple type
type Vars = M.Map String Scheme
newtype Env = Env { vars :: Vars }

type Substitution = M.Map TVar Type

data InferError
  = InfiniteType TVar Type
  | UnboundVariable String
  | UnificationError Type Type
  deriving (Show, Eq, Ord)

newtype Unique = Unique { count :: Int }
  deriving (Show, Eq, Ord)

type Infer a = forall m . (MonadError InferError m, MonadState Unique m) => m a


class Substitutable a where
  apply :: Substitution -> a -> a
  ftv   :: a -> S.Set TVar

instance Substitutable Type where
  apply _ (  TCon a      ) = TCon a
  apply s t@(TVar a      ) = M.findWithDefault t a s
  apply s (  t1 `TArr` t2) = apply s t1 `TArr` apply s t2

  ftv TCon{}         = S.empty
  ftv (TVar a      ) = S.singleton a
  ftv (t1 `TArr` t2) = ftv t1 `S.union` ftv t2

instance Substitutable Scheme where
  apply s (Forall as t) = Forall as $ apply s' t
    where s' = foldr M.delete s as
  ftv (Forall as t) = S.difference (ftv t) (S.fromList as)

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = foldr (S.union . ftv) S.empty

instance Substitutable Env where
  apply s env = env { vars = M.map (apply s) $ vars env }
  ftv env = ftv $ M.elems $ vars env


extendVars :: Env -> (String, Scheme) -> Env
extendVars env (x, s) = env { vars = M.insert x s $ vars env }


lookupVar :: Env -> String -> Infer (Substitution, Type)
lookupVar env x = do
  case M.lookup x $ vars env of
    Nothing -> throwError $ UnboundVariable x
    Just s  -> do
      t <- instantiate s
      return (M.empty, t)


letters :: [String]
letters = [1 ..] >>= flip replicateM ['a' .. 'z']

newTVar :: Infer Type
newTVar = do
  s <- get
  put s { count = count s + 1 }
  return $ TVar $ TV (letters !! count s)


instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const newTVar) as
  let s = M.fromList $ zip as as'
  return $ apply s t


compose :: Substitution -> Substitution -> Substitution
s1 `compose` s2 = M.map (apply s1) $ M.union s2 s1


occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = S.member a $ ftv t


bind :: TVar -> Type -> Infer Substitution
bind a t | t == TVar a     = return M.empty
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return $ M.singleton a t


unify :: Type -> Type -> Infer Substitution
unify (l `TArr` r) (l' `TArr` r') = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return (s2 `compose` s1)

unify (TVar a) t                 = bind a t
unify t        (TVar a)          = bind a t
unify (TCon a) (TCon b) | a == b = return M.empty
unify t1 t2                      = throwError $ UnificationError t1 t2


infer :: Env -> Exp -> Infer (Substitution, Type)
infer env Var { ename }         = lookupVar env ename

infer env Abs { eparam, ebody } = do
  tv <- newTVar
  let env' = extendVars env (eparam, Forall [] tv)
  (s1, t1) <- infer env' ebody
  return (s1, apply s1 tv `TArr` t1)

infer env App { eabs, earg } = do
  tv       <- newTVar
  (s1, t1) <- infer env eabs
  (s2, t2) <- infer (apply s1 env) earg
  s3       <- unify (apply s2 t1) (TArr t2 tv)
  return (s3 `compose` s2 `compose` s1, apply s3 tv)

infer env Assignment { eexp, ename } = case eexp of
  Abs{} -> do
    (s1, t1) <- infer env eexp
    s2       <- case M.lookup ename $ vars env of
      Just t2 -> instantiate t2 >>= unify t1
      Nothing -> return s1
    return (s2 `compose` s1, t1)
  _ -> infer env eexp

infer env LInt{}               = return (M.empty, TCon CNum)
infer env LStr{}               = return (M.empty, TCon CString)
infer env LBool{}              = return (M.empty, TCon CBool)

infer env TypedExp { etyping } = return (M.empty, typingsToType etyping)

infer _   _                    = undefined

typingsToType :: [Typing] -> Type
typingsToType [t     ] = typingToType t
typingsToType (t : xs) = TArr (typingToType t) (typingsToType xs)

typingToType :: Typing -> Type
typingToType (Typing t) | t == "Num"    = TCon CNum
                        | t == "Bool"   = TCon CBool
                        | t == "String" = TCon CString
                        | otherwise     = TVar $ TV t

initialEnv :: Env
initialEnv = Env
  { vars = M.fromList
             [ ( "==="
               , Forall [TV "a"]
               $      TVar (TV "a")
               `TArr` TVar (TV "a")
               `TArr` TCon CBool
               )
             , ("+", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
             , ("-", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
             , ("*", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
             , ("/", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
             ]
  }

inferExps :: Env -> [Exp] -> Infer [Type]
inferExps env [exp   ] = (: []) . snd <$> infer env exp
inferExps env (e : xs) = do
  r <- infer env e
  let env' = case e of
        Assignment { ename } -> extendVars env (ename, Forall [] $ snd r)
        TypedExp { eexp = Var { ename } } ->
          extendVars env (ename, Forall [] $ snd r)
        _ -> env
  (\n -> snd r : n) <$> inferExps env' xs

runInfer :: AST -> Either InferError [Type]
runInfer ast = fst <$> runExcept
  (runStateT (inferExps initialEnv $ aexps ast) Unique { count = 0 })
