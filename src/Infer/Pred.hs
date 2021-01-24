{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
module Infer.Pred where

import Infer.Type
import Infer.Substitute
import qualified Data.Map as M
import Control.Monad (msum)
import Infer.Unify
import Control.Monad.Except
import Infer.Infer
import Error.Error
import Explain.Reason
import Text.Show.Pretty (ppShow)
import Debug.Trace (trace)
import Data.Maybe
import Data.List


-- defined :: Maybe a -> Bool
-- defined (Just x) = True
-- defined Nothing  = False

-- overlap       :: Env -> Pred -> Pred -> Bool
-- overlap env p q = defined (unify env p q)


instance Unify Pred where
  unify = liftPred unify

instance Match Pred where
   match = liftPred match

addInterface :: Env -> Id -> [TVar] -> [Pred] -> Infer Env
addInterface env id tvs ps = case M.lookup id (envinterfaces env) of
  Just x  -> throwError $ InferError (InterfaceAlreadyDefined id) NoReason
  Nothing -> return env { envinterfaces = M.insert id (Interface tvs ps []) (envinterfaces env)}

-- Add test for overlap that should also test for kind of the given type !!
addInstance :: Env -> [Pred] -> Pred -> Infer Env
addInstance env ps p@(IsIn id ts) = case M.lookup id (envinterfaces env) of
  Nothing -> throwError $ InferError (InterfaceNotExisting id) NoReason

  Just (Interface tvs ps' is) -> do
    let ts' = TVar <$> tvs
    s <- match ts' ts
    mapM_ (isInstanceDefined env s) ps'
    return env { envinterfaces = M.insert
      id
      (Interface tvs ps' (Instance (ps :=> p) : is))
      (envinterfaces env)}


isInstanceDefined :: Env -> Substitution -> Pred -> Infer Bool
isInstanceDefined env subst (IsIn id ts) = do
  let is    = insts env id
      found = find (\(Instance (_ :=> (IsIn _ ts'))) -> apply subst ts' == apply subst ts) is
  case found of
    Just _  -> return True
    Nothing -> throwError $ InferError (NoInstanceFound id (apply subst $ head ts)) NoReason


liftPred :: ([Type] -> [Type] -> Infer a) -> Pred -> Pred -> Infer a
liftPred m (IsIn i ts) (IsIn i' ts')
         | i == i'   = m ts ts'
         | otherwise = throwError $ InferError FatalError NoReason


sig       :: Env -> Id -> [TVar]
sig env i   = case M.lookup i (envinterfaces env) of Just (Interface vs _ _) -> vs

super     :: Env -> Id -> [Pred]
super env i = case M.lookup i (envinterfaces env) of Just (Interface _ is _) -> is

insts     :: Env -> Id -> [Instance]
insts env i = case M.lookup i (envinterfaces env) of Just (Interface _ _ insts) -> insts

bySuper :: Env -> Pred -> [Pred]
bySuper env p@(IsIn i ts)
 = p : concatMap (bySuper env) supers
   where supers = apply s (super env i)
         s      = M.fromList $ zip (sig env i) ts

byInst                   :: Env -> Pred -> Infer [Pred]
byInst env p@(IsIn interface t)    = tryInsts (insts env interface)
   where
    tryInst (Instance (ps :=> h)) = do
        u <- match h p
        let ps' = apply u <$> ps
        return ps'
    tryInsts [] = case head t of
      TVar _ -> throwError $ InferError FatalError NoReason
      _ -> throwError $ InferError (NoInstanceFound interface (head t)) NoReason
    tryInsts (inst:is) = catchError (tryInst inst) (\e -> tryInsts is)

allM :: (Monad m, Foldable t) => (a -> m Bool) -> t a -> m Bool
allM f = foldM (\b a -> f a >>= (return . (&& b))) True

entail :: Env -> [Pred] -> Pred -> Infer Bool
entail env ps p = do
  tt <- catchError (byInst env p >>= allM (entail env ps)) (\case
      InferError FatalError _ -> return False
      e -> throwError e
      )
  return $ any ((p `elem`) . bySuper env) ps || tt

-----------------------------------------------------------------------------

simplify   :: ([Pred] -> Pred -> Bool) -> [Pred] -> [Pred]
simplify ent = loop []
 where loop rs []                      = rs
       loop rs (p:ps) | ent (rs++ps) p = loop rs ps
                      | otherwise      = loop (p:rs) ps

reduce      :: Env -> [Pred] -> Infer [Pred]
reduce env ps = do
  withoutTauts <- elimTauts env ps
  return $ simplify (scEntail env) withoutTauts

elimTauts   :: Env -> [Pred] -> Infer [Pred]
elimTauts env = filterM ((not <$>) . entail env [])

scEntail        :: Env -> [Pred] -> Pred -> Bool
scEntail env ps p = any (p `elem`) (map (bySuper env) ps)