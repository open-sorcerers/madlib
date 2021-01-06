{-# LANGUAGE FlexibleInstances #-}
module Infer.Substitute where

import qualified Data.Map                      as M
import qualified Data.Set                      as S
import           Data.Foldable                  ( Foldable(foldl') )
import           Infer.Type
import           Debug.Trace                    ( trace )
import           Text.Show.Pretty               ( ppShow )


class Substitutable a where
  apply :: Env -> Substitution -> a -> a
  ftv   :: a -> S.Set TVar


instance Substitutable Pred where
  apply env s (IsIn i ts) = IsIn i (apply env s ts)
  ftv (IsIn i ts) = ftv ts

instance Substitutable t => Substitutable (Qual t) where
  apply env s (ps :=> t) = apply env s ps :=> apply env s t
  ftv (ps :=> t) = ftv ps `S.union` ftv t

instance Substitutable Type where
  apply env _ (  TCon a      ) = TCon a
  apply env s t@(TVar a      ) = M.findWithDefault t a s
  apply env s (  t1 `TApp` t2) = apply env s t1 `TApp` apply env s t2
  apply env s rec@(TRecord fields open) =
    let applied = TRecord (apply env s <$> fields) open
    in  if rec == applied then applied else apply env s applied
  apply env s t = t

  ftv TCon{}              = S.empty
  ftv (TVar a           ) = S.singleton a
  ftv (t1      `TApp` t2) = ftv t1 `S.union` ftv t2
  ftv (TRecord fields _ ) = foldl' (\s v -> S.union s $ ftv v) S.empty fields
  ftv t                   = S.fromList []

instance Substitutable Scheme where
  apply env s (Forall ks t) = Forall ks $ apply env s t
  ftv (Forall _ t) = ftv t

instance Substitutable a => Substitutable [a] where
  apply env = fmap . apply env
  ftv = foldr (S.union . ftv) S.empty

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
