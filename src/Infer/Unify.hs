{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Unify where

import           Control.Monad.Except
import qualified Data.Map                      as M
import qualified Data.Set                      as S

import           Infer.Type
import           Infer.Substitute
import           Error.Error
import Infer.Env (lookupInstance)
import Debug.Trace (trace)
import Text.Show.Pretty (ppShow)
import Data.Char (isLower)


occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = S.member a $ ftv t


bind :: Env -> [String] -> TVar -> Type -> Either TypeError Substitution
bind _ constraints tv t@(TVar constraints' tv') | (not . null) constraints =
  return $ M.singleton tv' (TVar ((S.toList . S.fromList) (constraints <> constraints')) tv')
  -- return $ M.singleton tv' (TVar ((S.toList . S.fromList) (constraints <> constraints')) tv')
bind env constraints tv t | t == TVar [] tv  = return M.empty
                          | occursCheck tv t = throwError $ InfiniteType tv t
                          | otherwise        =
  if null constraints
    then return $ M.singleton tv t
    else
      let inst = lookupInstance env (head constraints) t
      in  case inst of
        Just _ -> return $ M.singleton tv t
        _ -> throwError $ NoInstanceFound (head constraints) t


cleanTCompMain :: String -> String
cleanTCompMain = reverse . takeWhile (/= '.') . reverse

unify :: Env -> Type -> Type -> Either TypeError Substitution
unify env (l `TArr` r) (l' `TArr` r') = do
  s1 <- unify env l l'
  s2 <- unify env (apply env s1 r) (apply env s1 r')
  return $ compose env s1 s2

unify env (TTuple elems) (TTuple elems') = do
  if length elems == length elems'
    then unifyVars env M.empty (zip elems elems')
    else throwError $ UnificationError (TTuple elems) (TTuple elems')

unify env (TComp astPath main vars) (TComp astPath' main' vars')
  | (cleanTCompMain main == cleanTCompMain main')
    && astPath
    == astPath'
    && length vars
    == length vars'
    || (isLower . head) main || (isLower . head) main'
  = let z = zip vars vars' in unifyVars env M.empty z
  | otherwise
  = throwError
    $ UnificationError (TComp astPath main vars) (TComp astPath' main' vars')

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

unify env (TVar constraints tv) t               = bind env constraints tv t
unify env t        (TVar constraints tv)        = bind env constraints tv t
unify _ (TCon a) (TCon b) | a == b = return M.empty
unify _ (TComp _ _ _) (TGenComp _ _ _) = return M.empty
unify _ (TGenComp _ _ _) (TComp _ _ _) = return M.empty
unify _ t1 t2                      = throwError $ UnificationError t1 t2


unifyVars :: Env -> Substitution -> [(Type, Type)] -> Either TypeError Substitution
unifyVars env s ((tp, tp') : xs) = do
  s1 <- unify env tp tp'
  unifyVars env (compose env s1 s) xs
unifyVars _ s _ = return s


unifyElems :: Env -> Type -> [Type] -> Either TypeError Substitution
unifyElems _ _ []          = return M.empty
unifyElems env t [t'     ] = unify env t t'
unifyElems env t (t' : xs) = do
  s1 <- unify env t t'
  s2 <- unifyElems env t xs
  return $ compose env s1 s2

-- unifyOrSwap :: Env -> Type -> Type -> Either TypeError (Substitution, Maybe Type)
-- unifyOrSwap env t1 t2 = case (t1, t2) of
--   (t@(TComp _ _ _), TGenComp _ _ _) -> return (M.empty, Just t)
--   (TGenComp _ _ _, t@(TComp _ _ _)) -> return (M.empty, Just t)
--   _ -> (,Nothing) <$> unify env t1 t2
