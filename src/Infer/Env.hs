{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Env where

import qualified Data.Map                      as M
import           Infer.Type                    as Ty
import           AST.Source                    as Src
import           Control.Monad.Except           ( MonadError(throwError) )
import           Infer.Instantiate
import           Infer.ADT
import           Infer.Infer
import           Explain.Reason
import           Error.Error
import qualified Data.Set                      as S
import           Infer.Substitute               ( Substitutable(ftv) )
import           Infer.Typing                   (collectVars, typingToScheme,  typingToType )
import           Data.List                      ( isInfixOf
                                                , find
                                                )
import           Data.Maybe                     (mapMaybe,  fromMaybe )
import           Text.Show.Pretty               ( ppShow )
import           Debug.Trace                    ( trace )
import           Infer.Scheme                   (quantify,  toScheme )
import Control.Monad (foldM)
import Control.Monad (msum)
import Infer.Pred (addInstance, addInterface)


lookupVar :: Env -> String -> Infer Scheme
lookupVar env x
  | "." `isInfixOf` x = do
    let (namespace, name) = break (== '.') x
    case M.lookup namespace (envvars env) of
      Just s -> do
        h <- instantiate s
        let (TRecord fields _) = qualType h

        case M.lookup (tail name) fields of
          Just t  -> return (toScheme t)
          Nothing -> throwError $ InferError (UnboundVariable x) NoReason

      Nothing -> throwError $ InferError (UnboundVariable x) NoReason
  | otherwise = case M.lookup x (envvars env <> envmethods env) of
    Just x  -> return x
    Nothing -> throwError $ InferError (UnboundVariable x) NoReason


extendVars :: Env -> (String, Scheme) -> Env
extendVars env (x, s) = env { envvars = M.insert x s $ envvars env }


safeExtendVars :: Env -> (String, Scheme) -> Infer Env
safeExtendVars env (i, sc) = case M.lookup i (envvars env) of
  Just _  -> throwError $ InferError (NameAlreadyDefined i) NoReason
  Nothing -> return $ extendVars env (i, sc)


mergeVars :: Env -> Vars -> Env
mergeVars env vs = env { envvars = envvars env <> vs }


initialEnv :: Env
initialEnv = Env
  { envvars        = M.fromList
    [ ("==", Forall [Star] $ [] :=> (TGen 0 `fn` TGen 0 `fn` tBool))
    , ("&&", Forall [] $ [] :=> (tBool `fn` tBool `fn` tBool))
    , ("||", Forall [] $ [] :=> (tBool `fn` tBool `fn` tBool))
    , ("!" , Forall [] $ [] :=> (tBool `fn` tBool))
    , (">" , Forall [Star] $ [] :=> (TGen 0 `fn` TGen 0 `fn` tBool))
    , ("<" , Forall [Star] $ [] :=> (TGen 0 `fn` TGen 0 `fn` tBool))
    , (">=", Forall [Star] $ [] :=> (TGen 0 `fn` TGen 0 `fn` tBool))
    , ("<=", Forall [Star] $ [] :=> (TGen 0 `fn` TGen 0 `fn` tBool))
    , ("++", Forall [] $ [] :=> (tStr `fn` tStr `fn` tStr))
    , ("+" , Forall [] $ [] :=> (tNumber `fn` tNumber `fn` tNumber))
    , ("-" , Forall [] $ [] :=> (tNumber `fn` tNumber `fn` tNumber))
    , ("*" , Forall [] $ [] :=> (tNumber `fn` tNumber `fn` tNumber))
    , ("/" , Forall [] $ [] :=> (tNumber `fn` tNumber `fn` tNumber))
    , ("%" , Forall [] $ [] :=> (tNumber `fn` tNumber `fn` tNumber))
    , ( "|>"
      , Forall [Star, Star]
      $   []
      :=> (TGen 0 `fn` (TGen 0 `fn` TGen 1) `fn` TGen 1)
      )
    , ("show", Forall [Star] $ [IsIn "Show" [TGen 0]] :=> (TGen 0 `fn` tStr))
    ]
  , envtypes       = M.fromList
                       [ ("List" , tList)
                       , ("(,)"  , tTuple2)
                       , ("(,,)" , tTuple3)
                       , ("(,,,)", tTuple4)
                       ]
  , envinterfaces  = M.fromList
      [ ("Show", Ty.Interface [TV "a" Star] [] [Ty.Instance $ [] :=> IsIn "Show" [tNumber], Ty.Instance $ [] :=> IsIn "Show" [tBool], Ty.Instance $ [IsIn "Show" [TVar (TV "a" Star)]] :=> IsIn "Show" [TApp (TCon (TC "Maybe" (Kfun Star Star))) (TVar (TV "a" Star))]])
      ]
  , envmethods = M.empty
  , envcurrentpath = ""
  }

solveInterfaces :: Env -> [Src.Interface] -> Infer Env
solveInterfaces = foldM solveInterface


solveInterface :: Env -> Src.Interface -> Infer Env
solveInterface env interface = case interface of
  Src.Interface n tv ms -> do
    ts  <- mapM (typingToType env) ms
    let ts' = addConstraints n tv <$> ts

    let tvs = mapMaybe (searchVarInType tv) (M.elems ts)

    env' <- if null tvs
      then throwError $ InferError FatalError NoReason
      else addInterface env n [(\(TVar tv) -> tv) . head $ tvs] []

    return env' { envvars = envvars env <> ts', envmethods = envmethods env <> ts' }


addConstraints :: Id -> Id -> Type -> Scheme
addConstraints n tv t =
  let tv' = searchVarInType tv t
      qt  = case tv' of
        Just tv'' -> [IsIn n [tv'']] :=> t
        Nothing   -> [] :=> t
      vars = collectVars t
  in  quantify vars qt


solveInstances :: Env -> [Src.Instance] -> Infer Env
solveInstances = foldM solveInstance


solveInstance :: Env -> Src.Instance -> Infer Env
solveInstance env inst = case inst of
  Src.Instance n typing _ -> do
    t <- typingToType env typing
    addInstance env [] $ IsIn n [t]


buildInitialEnv :: Env -> AST -> Infer Env
buildInitialEnv priorEnv AST { atypedecls, ainterfaces, ainstances, apath = Just apath }
  = do
    tadts <- buildTypeDecls priorEnv apath atypedecls
    vars  <- resolveTypeDecls priorEnv apath tadts atypedecls
    env   <- solveInterfaces priorEnv ainterfaces
    env'  <- solveInstances (env { envtypes = M.union (envtypes initialEnv) tadts }) ainstances
    return env' { envvars        = envvars initialEnv <> vars <> envvars env
                , envtypes       = M.union (envtypes initialEnv) tadts
                , envcurrentpath = apath
                }
