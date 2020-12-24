{-# LANGUAGE LambdaCase #-}
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
import Infer.Typing (typingToType)
import Data.List (find)
import Data.Maybe (fromMaybe)
import Text.Show.Pretty (ppShow)
import Debug.Trace (trace)



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

lookupInstance :: Env -> String -> Type -> Maybe Ty.Instance
lookupInstance env interface ty =
  let instances = envinstances env
  in  find (\(Ty.Instance ty' interface' _ _) -> ty' `typeEq` ty && interface == interface') instances

typeEq :: Type -> Type -> Bool
typeEq t1 t2 = case (t1, t2) of
  (TComp p n _, TComp p' n' _) -> p == p' && n == n'
  _ -> t1 == t2

lookupInstanceMethod :: Env -> Type -> String -> String -> Infer Src.Exp
lookupInstanceMethod env instanceType interface name = do
  let inst = find (\case Ty.Instance t interface' _ _ -> interface == interface' && t `typeEq` (trace ("INST-TYPE: "<>ppShow instanceType<>"\nINT-NAME: "<>ppShow interface<>"\nMETHOD: "<>ppShow name) instanceType)) (envinstances env)
  case inst of
    Nothing -> throwError $ InferError (UnboundVariable name) NoReason
    Just (Ty.Instance _ _ dict _) -> return $ fromMaybe undefined $ M.lookup name dict

initialEnv :: Env
initialEnv = Env
  { envvars        = M.fromList
    [ ( "=="
      , Forall [TV "a"] $ TVar [] (TV "a") `TArr` TVar [] (TV "a") `TArr` TCon CBool
      )
    , ("&&", Forall [] $ TCon CBool `TArr` TCon CBool `TArr` TCon CBool)
    , ("||", Forall [] $ TCon CBool `TArr` TCon CBool `TArr` TCon CBool)
    , ("!" , Forall [] $ TCon CBool `TArr` TCon CBool)
    , ( ">"
      , Forall [TV "a"] $ TVar [] (TV "a") `TArr` TVar [] (TV "a") `TArr` TCon CBool
      )
    , ( "<"
      , Forall [TV "a"] $ TVar [] (TV "a") `TArr` TVar [] (TV "a") `TArr` TCon CBool
      )
    , ( ">="
      , Forall [TV "a"] $ TVar [] (TV "a") `TArr` TVar [] (TV "a") `TArr` TCon CBool
      )
    , ( "<="
      , Forall [TV "a"] $ TVar [] (TV "a") `TArr` TVar [] (TV "a") `TArr` TCon CBool
      )
    , ("++", Forall [] $ TCon CString `TArr` TCon CString `TArr` TCon CString)
    , ("+" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("-" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("*" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("/" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ("%" , Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
    , ( "|>"
      , Forall [TV "a", TV "b"]
      $      TVar [] (TV "a")
      `TArr` (TVar [] (TV "a") `TArr` TVar [] (TV "b"))
      `TArr` TVar [] (TV "b")
      )
    , ( "asList"
      , Forall [TV "a"] $ TArr (TVar [] $ TV "a") $ TComp "Prelude"
                                                       "List"
                                                       [TVar [] $ TV "a"]
      )
    , ( "List"
      , Forall [TV "a"] $ TArr (TVar [] $ TV "a") $ TComp "Prelude"
                                                       "List"
                                                       [TVar [] $ TV "a"]
      )
    ]
  , envtypes = M.fromList [("List", TComp "Prelude" "List" [TVar [] $ TV "a"])]
  , envimports     = M.empty
  , envinterfaces = []
  , envinstances = []
  , envcurrentpath = ""
  }


solveInstances :: Env -> [Src.Instance] -> Infer [Ty.Instance]
solveInstances env = mapM (solveInstance env)

solveInstance :: Env -> Src.Instance -> Infer Ty.Instance
solveInstance env inst = case inst of
  Src.Instance cls t dict -> do
    t' <- typingToType env t
    return $ Ty.Instance t' cls dict []

solveInterfaces :: Env -> [Src.Interface] -> Infer [Ty.Interface]
solveInterfaces env = mapM (solveInterface env)

solveInterface :: Env -> Src.Interface -> Infer Ty.Interface
solveInterface env interface = case interface of
  Src.Interface name var methods -> do
    ts <- mapM (typingToType env) methods
    let ts' = M.map (addConstraints name var) ts
    return $ Ty.Interface name var ts'

addConstraints :: String -> String -> Type -> Type
addConstraints interfaceName var t = case t of
  TVar _ (TV n) -> if n == var then TVar [interfaceName] (TV n) else t
  TArr l r -> TArr (addConstraints interfaceName var l) (addConstraints interfaceName var r)
  TGenComp name _ args ->
    if name == var
      then TGenComp name [interfaceName] (addConstraints interfaceName var <$> args)
      else TGenComp name [] (addConstraints interfaceName var <$> args)
  _ -> t

getInterfaceMethods :: Ty.Interface -> M.Map String Scheme
getInterfaceMethods interface = case interface of
  Ty.Interface _ _ methods -> M.map (\m -> Forall (S.toList $ ftv m) m) methods

getInterfacesMethods :: [Ty.Interface] -> M.Map String Scheme
getInterfacesMethods = foldr (M.union . getInterfaceMethods) M.empty

buildInitialEnv :: Env -> AST -> Infer Env
buildInitialEnv priorEnv AST { atypedecls, ainterfaces, ainstances, apath = Just apath } = do
  tadts      <- buildTypeDecls priorEnv apath atypedecls
  vars       <- resolveTypeDecls priorEnv apath tadts atypedecls
  interfaces <- solveInterfaces priorEnv ainterfaces
  instances  <- solveInstances priorEnv ainstances
  let allVars = M.union (M.union (envvars initialEnv) vars) (getInterfacesMethods interfaces)
  return Env { envvars        = (trace ("INSTANCES: "<>ppShow instances<>"\nINTERFACES: "<>ppShow interfaces) allVars)
             , envtypes       = M.union (envtypes initialEnv) tadts
             , envimports     = M.empty
             , envinterfaces  = interfaces
             , envinstances   = instances
             , envcurrentpath = apath
             }
