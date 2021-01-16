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
  | otherwise = case M.lookup x (envvars env) of
    Just x  -> return x
    Nothing -> throwError $ InferError (UnboundVariable x) NoReason


extendVars :: Env -> (String, Scheme) -> Env
extendVars env (x, s) = env { envvars = M.insert x s $ envvars env }


mergeVars :: Env -> Vars -> Env
mergeVars env vs = env { envvars = M.union (envvars env) vs }

-- lookupInstance :: Env -> String -> Type -> Maybe Ty.Instance
-- lookupInstance env interface ty =
--   let instances = envinstances env
--   in  find (\(Ty.Instance ty' interface' _ _) -> ty' `typeEq` ty && interface == interface') instances

-- lookupInstanceMethod :: Env -> Type -> String -> String -> Infer Src.Exp
-- lookupInstanceMethod env instanceType interface name = do
--   let inst = find (\case Ty.Instance t interface' _ _ -> interface == interface' && t `typeEq` instanceType) (envinstances env)
--   case inst of
--     Nothing -> throwError $ InferError (UnboundVariable name) NoReason
--     Just (Ty.Instance _ _ dict _) -> return $ fromMaybe undefined $ M.lookup name dict

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
    , ("map", Forall [Star, Star, Kfun Star Star] $ [IsIn "Functor" [TGen 2]] :=> ((TGen 0 `fn` TGen 1) `fn` TApp (TGen 2) (TGen 0) `fn` TApp (TGen 2) (TGen 1)))
    ]
  , envtypes       = M.fromList
                       [ ("List" , tList)
                       , ("(,)"  , tTuple2)
                       , ("(,,)" , tTuple3)
                       , ("(,,,)", tTuple4)
                       ]
  , envinterfaces  = M.fromList
      [ ("Show", Ty.Interface [TV "a" Star] [] [Ty.Instance $ [] :=> IsIn "Show" [tNumber], Ty.Instance $ [] :=> IsIn "Show" [tBool], Ty.Instance $ [IsIn "Show" [TVar (TV "a" Star)]] :=> IsIn "Show" [TApp (TCon (TC "Maybe" (Kfun Star Star))) (TVar (TV "a" Star))]])
      , ("Functor", Ty.Interface [TV "m" (Kfun Star Star)] []
          [ Ty.Instance $ [] :=> IsIn "Functor" [TCon (TC "Maybe" (Kfun Star Star))]
          , Ty.Instance $ [] :=> IsIn "Functor" [tList]
          ])
      ]
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

    return env' { envvars = envvars env <> ts' }

addConstraints :: Id -> Id -> Type -> Scheme
addConstraints n tv t =
  let tv' = searchVarInType tv t
      qt  = case tv' of
        Just tv'' -> [IsIn n [tv'']] :=> t
        Nothing   -> [] :=> t
      vars = collectVars t
  in  quantify vars qt

searchVarInType :: Id -> Type -> Maybe Type
searchVarInType id t = case t of
  TVar (TV n _) -> if n == id then Just t else Nothing
  TCon _        -> Nothing
  TApp l r      ->
    let l' = searchVarInType id l
        r' = searchVarInType id r
    in  case (l', r') of
      (Just x, _) -> Just x
      (_, Just x) -> Just x
      _           -> Nothing


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
    env   <- solveInterfaces initialEnv ainterfaces
    env'  <- solveInstances (env { envtypes = M.union (envtypes initialEnv) tadts }) ainstances
    return env' { envvars        = envvars initialEnv <> vars <> envvars env
               , envtypes       = M.union (envtypes initialEnv) tadts
              --  , envinterfaces  = envinterfaces initialEnv
               , envcurrentpath = apath
               }
