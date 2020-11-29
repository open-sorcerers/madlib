{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Env where

import qualified Data.Map                      as M
import           Infer.Type
import           AST.Source
import           Control.Monad.Except           ( MonadError(throwError) )
import           Infer.Instantiate
import           Infer.ADT
import           Infer.Infer
import           Explain.Reason
import           Error.Error
import qualified Data.Set                      as S
import           Infer.Substitute               ( Substitutable(ftv) )



lookupVar :: Env -> String -> Infer (Substitution, Type)
lookupVar env x = do
  case M.lookup x $ envvars env of
    Nothing -> case M.lookup x $ envimports env of
      Nothing -> throwError $ InferError (UnboundVariable x) NoReason
      Just s  -> do
        t <- instantiate $ Forall (S.toList $ ftv s) s
        return (M.empty, t)

    Just s -> do
      t <- instantiate s
      return (M.empty, t)


extendVars :: Env -> (String, Scheme) -> Env
extendVars env (x, s) = env { envvars = M.insert x s $ envvars env }


initialEnv :: Env
initialEnv = Env
  { envvars        = M.fromList
    [ ( "=="
      , Forall [TV "a"] $ TVar (TV "a") `TArr` TVar (TV "a") `TArr` TCon CBool
      )
    , ("&&", Forall [] $ TCon CBool `TArr` TCon CBool `TArr` TCon CBool)
    , ("||", Forall [] $ TCon CBool `TArr` TCon CBool `TArr` TCon CBool)
    , ("!" , Forall [] $ TCon CBool `TArr` TCon CBool)
    , ( ">"
      , Forall [TV "a"] $ TVar (TV "a") `TArr` TVar (TV "a") `TArr` TCon CBool
      )
    , ( "<"
      , Forall [TV "a"] $ TVar (TV "a") `TArr` TVar (TV "a") `TArr` TCon CBool
      )
    , ( ">="
      , Forall [TV "a"] $ TVar (TV "a") `TArr` TVar (TV "a") `TArr` TCon CBool
      )
    , ( "<="
      , Forall [TV "a"] $ TVar (TV "a") `TArr` TVar (TV "a") `TArr` TCon CBool
      )
    , ("++", Forall [] $ TCon CString `TArr` TCon CString `TArr` TCon CString)
    , ("+" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("-" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("*" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("/" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("%" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ( "|>"
      , Forall [TV "a", TV "b"]
      $      TVar (TV "a")
      `TArr` (TVar (TV "a") `TArr` TVar (TV "b"))
      `TArr` TVar (TV "b")
      )
    , ( "asList"
      , Forall [TV "a"] $ TArr (TVar $ TV "a") $ TComp "Prelude"
                                                       "List"
                                                       [TVar $ TV "a"]
      )
    , ( "List"
      , Forall [TV "a"] $ TArr (TVar $ TV "a") $ TComp "Prelude"
                                                       "List"
                                                       [TVar $ TV "a"]
      )
    ]
  , envtypes = M.fromList [("List", TComp "Prelude" "List" [TVar $ TV "a"])]
  , envimports     = M.empty
  , envcurrentpath = ""
  }


-- TODO: Should we build imported names here ?
buildInitialEnv :: Env -> AST -> Infer Env
buildInitialEnv priorEnv AST { atypedecls, apath = Just apath } = do
  tadts <- buildTypeDecls priorEnv apath atypedecls
  vars  <- resolveTypeDecls priorEnv apath tadts atypedecls
  let allVars = M.union (envvars initialEnv) vars
  return Env { envvars        = allVars
             , envtypes       = M.union (envtypes initialEnv) tadts
             , envimports     = M.empty
             , envcurrentpath = apath
             }
