{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Unify where

import           Control.Monad.Except
import qualified Data.Map                      as M
import qualified Data.Set                      as S

import           Infer.Type
import           Infer.Substitute
import           Error.Error


occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = S.member a $ ftv t


varBind :: TVar -> Type -> Either TypeError Substitution
varBind tv t | t == TVar tv      = return M.empty
             | tv `elem` ftv t   = throwError $ InfiniteType tv t
             | kind tv /= kind t = throwError $ KindError (TVar tv) t
             | otherwise         = return $ M.singleton tv t

unify :: Env -> Type -> Type -> Either TypeError Substitution
unify env (l `TApp` r) (l' `TApp` r') = do
  s1 <- unify env l l'
  s2 <- unify env (apply env s1 r) (apply env s1 r')
  return $ compose env s1 s2

unify env (TRecord fields open) (TRecord fields' open')
  | open || open' = do
    let extraFields    = M.difference fields fields'
        extraFields'   = M.difference fields' fields
        updatedFields  = M.union fields extraFields'
        updatedFields' = M.union fields' extraFields
        types          = M.elems updatedFields
        types'         = M.elems updatedFields'
        z              = zip types types'
    unifyVars env M.empty z
  | M.difference fields fields' /= M.empty = throwError
  $ UnificationError (TRecord fields open) (TRecord fields' open')
  | otherwise = do
    let types  = M.elems fields
        types' = M.elems fields'
        z      = zip types types'
    unifyVars env M.empty z

unify env (TVar tv) t              = varBind tv t
unify env t         (TVar tv)      = varBind tv t
unify _ (TCon a) (TCon b) | a == b = return M.empty
unify _ t1 t2                      = throwError $ UnificationError t1 t2


unifyVars
  :: Env -> Substitution -> [(Type, Type)] -> Either TypeError Substitution
unifyVars env s ((tp, tp') : xs) = do
  s1 <- unify env tp tp'
  unifyVars env (compose env s1 s) xs
unifyVars _ s _ = return s


unifyElems :: Env -> [Type] -> Either TypeError Substitution
unifyElems env []      = Right M.empty
unifyElems env [ts   ] = Right M.empty
unifyElems env (h : r) = unifyElems' env h r

unifyElems' :: Env -> Type -> [Type] -> Either TypeError Substitution
unifyElems' _   _ []        = return M.empty
unifyElems' env t [t'     ] = unify env t t'
unifyElems' env t (t' : xs) = do
  s1 <- unify env t t'
  s2 <- unifyElems' env t xs
  return $ compose env s1 s2

