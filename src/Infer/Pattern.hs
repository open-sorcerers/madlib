{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Pattern where

import Infer.Type
import qualified AST.Source as Src
import Infer.Infer
import qualified Data.Map as M
import Explain.Meta
import qualified Utils.Tuple as T
import Infer.Instantiate
import Infer.Scheme
import Infer.Unify
import Infer.Env
import Error.Error
import Explain.Reason
import Control.Monad.Except
import Infer.Substitute


inferPatterns :: Env -> [Src.Pattern] -> Infer ([Pred], Vars, [Type])
inferPatterns env pats = do
  psasts <- mapM (inferPattern env) pats
  let ps = concat [ ps' | (ps', _, _) <- psasts ]
      as = foldr M.union M.empty [ vars | (_, vars, _) <- psasts ]
      ts = [ t | (_, _, t) <- psasts ]
  return (ps, as, ts)

inferPattern :: Env -> Src.Pattern -> Infer ([Pred], Vars, Type)
inferPattern env (Meta _ _ pat) = case pat of
  Src.PNum _ -> return ([], M.empty, tNumber)
  Src.PBool _ -> return ([], M.empty, tBool)
  Src.PStr _ -> return ([], M.empty, tStr)

  Src.PCon n -> return ([], M.empty, TCon $ TC n Star)

  Src.PVar i -> do
    v <- newTVar Star
    return ([], M.singleton i (toScheme v), v)

  Src.PAny -> do
    v <- newTVar Star
    return ([], M.empty, v)

  Src.PTuple pats -> do
    ti <- mapM (inferPattern env) pats
    let ts   = T.lst <$> ti
    let ps   = foldr (<>) [] (T.beg <$> ti)
    let vars = foldr (<>) M.empty (T.mid <$> ti)

    let tupleT = getTupleCtor (length ts)
    let t = foldl TApp tupleT ts

    return (ps, vars, t)
  
  Src.PList pats -> do
    li <- mapM (inferPListItem env) pats
    tv <- newTVar Star
    let ts   = if null li then [tv] else T.lst <$> li
    let ps   = foldr (<>) [] (T.beg <$> li)
    let vars = foldr (<>) M.empty (T.mid <$> li)

    s <- case unifyElems (mergeVars env vars) ts of
      Right r -> return r
      Left e -> throwError $ InferError e NoReason

    return (ps, M.map (apply env s) vars, TApp tList (apply env s (head ts)))

    where
      inferPListItem :: Env -> Src.Pattern -> Infer ([Pred], Vars, Type)
      inferPListItem env pat@(Meta _ _ p) = case p of
        Src.PSpread (Meta _ _ (Src.PVar i)) -> do
          tv <- newTVar Star
          let t' = TApp tList tv
          return ([], M.singleton i (toScheme t'), tv)
        _ -> inferPattern env pat

  Src.PRecord pats -> do
    li <- mapM (inferFieldPattern env) pats
    let vars = foldr (<>) M.empty $ T.mid . snd <$> M.toList li
    let ps   = foldr (<>) [] $ T.beg . snd <$> M.toList li
    let ts   = T.lst . snd <$> M.toList li

    return (ps, vars, TRecord (M.map T.lst li) True)

    where
      inferFieldPattern :: Env -> Src.Pattern -> Infer ([Pred], Vars, Type)
      inferFieldPattern env pat@(Meta _ _ p) = case p of
        Src.PSpread (Meta _ _ (Src.PVar i)) -> do
          tv <- newTVar Star
          return ([], M.singleton i (toScheme tv), tv)

        _ -> inferPattern env pat

  Src.PCtor n pats -> do
    (ps, vars, ts) <- inferPatterns env pats
    tv             <- newTVar Star
    sc             <- lookupVar env n
    (ps' :=> t)    <- instantiate sc
    s              <- case unify env t (foldr fn tv ts) of
      Right r -> return r
      Left e -> throwError $ InferError e NoReason

    return (ps <> ps', vars, apply env s tv)