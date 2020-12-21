module Infer.Substitute where

import qualified Data.Map                      as M
import qualified Data.Set                      as S
import           Data.Foldable                  ( Foldable(foldl') )
import           Infer.Type


class Substitutable a where
  apply :: Env -> Substitution -> a -> a
  ftv   :: a -> S.Set TVar

instance Substitutable Type where
  apply env _ (  TCon a             ) = TCon a
  apply env s t@(TVar constraints a ) = case M.findWithDefault t a s of
    TVar constraints' a' -> TVar (constraints <> constraints') a'
    other -> other
  apply env s (  t1 `TArr` t2       ) = apply env s t1 `TArr` apply env s t2
  apply env s (  TComp src main vars) = TComp src main (apply env s <$> vars)
  apply env s (  TRecord fields open) = TRecord (apply env s <$> fields) open
  apply env s (  TTuple elems       ) = TTuple (apply env s <$> elems)

  ftv TCon{}             = S.empty
  ftv (TVar _ a        ) = S.singleton a
  ftv (t1 `TArr` t2    ) = ftv t1 `S.union` ftv t2
  ftv (TComp _ _ vars  ) = foldl' (\s v -> S.union s $ ftv v) S.empty vars
  ftv (TRecord fields _) = foldl' (\s v -> S.union s $ ftv v) S.empty fields
  ftv (TTuple elems    ) = foldl' (\s v -> S.union s $ ftv v) S.empty elems

instance Substitutable Scheme where
  apply env s (Forall as t) = Forall as $ apply env s' t
    where s' = foldr M.delete s as
  ftv (Forall as t) = S.difference (ftv t) (S.fromList as)

instance Substitutable a => Substitutable [a] where
  apply env = fmap . apply env
  ftv   = foldr (S.union . ftv) S.empty

instance Substitutable Env where
  apply env' s env = env { envvars = M.map (apply env' s) $ envvars env }
  ftv env = ftv $ M.elems $ envvars env

compose :: Env -> Substitution -> Substitution -> Substitution
compose env s1 s2 = M.map (apply env s1) $ M.unionsWith mergeTypes [s2, s1]
 where
  mergeTypes :: Type -> Type -> Type
  mergeTypes t1 t2 = case (t1, t2) of
    (TRecord fields1 open1, TRecord fields2 open2) ->
      TRecord (M.union fields1 fields2) (open1 || open2)
    (t, _) -> t


removeRecordTypes :: Substitution -> Substitution
removeRecordTypes = M.filter notRecord
 where
  notRecord :: Type -> Bool
  notRecord t = case t of
    TRecord _ _ -> False
    _           -> True
