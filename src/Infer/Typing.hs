{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Typing where

import qualified AST.Source                    as Src
import           Infer.Type
import           Explain.Meta
import           Infer.Infer
import           Data.Char                      ( isLower )
import qualified Data.Map                      as M
import           Control.Monad.Except           ( MonadError(throwError) )
import           Error.Error
import           Explain.Reason
import           Infer.Substitute
import Infer.Scheme (quantify)
import Debug.Trace (trace)
import Text.Show.Pretty (ppShow)
import Infer.Instantiate (newTVar)


typingToScheme :: Env -> Src.Typing -> Infer Scheme
typingToScheme env typing = do
  t <- typingToType env typing
  let vars = collectVars t
  return $ quantify vars ([] :=> t)


typingToType :: Env -> Src.Typing -> Infer Type
typingToType env (Meta _ _ (Src.TRSingle t))
  | t == "Number" = return tNumber
  | t == "Boolean" = return tBool
  | t == "String" = return tStr
  | t == "()" = return tUnit
  | isLower $ head t = return (TVar $ TV t Star)
  | otherwise = do
    h <- lookupADT env t
    case h of
      (TAlias _ _ _ t          ) -> return h
      t -> return t


typingToType env (Meta info area (Src.TRComp t ts)) = do
  h   <- typingToType env (Meta info area $ Src.TRSingle t)
  params  <- mapM (typingToType env) ts
  params' <- mapM (`updateAliasVars` []) params
  case h of
    TAlias _ _ _ _ -> updateAliasVars h params'

    _ -> return $ foldl TApp h params'

typingToType env (Meta _ _ (Src.TRArr l r)) = do
  l' <- typingToType env l
  r' <- typingToType env r
  return $ l' `fn` r'

typingToType env (Meta _ _ (Src.TRRecord fields)) = do
  fields' <- mapM (typingToType env) fields
  return $ TRecord fields' False

typingToType env (Meta _ _ (Src.TRTuple elems)) = do
  elems' <- mapM (typingToType env) elems
  return $ TTuple elems'

lookupADT :: Env -> String -> Infer Type
lookupADT env x = do
  case M.lookup x $ envtypes env of
    Nothing -> throwError $ InferError (UnknownType x) NoReason
    Just x  -> return x


collectVars :: Type -> [TVar]
collectVars t = case t of
  TVar tv  -> [tv]
  TCon _   -> []
  TApp l r -> collectVars l <> collectVars r
  TRecord fs _ -> concat $ collectVars <$> M.elems fs
  TTuple ts -> concat $ collectVars <$> ts
  _ -> []


updateAliasVars :: Type -> [Type] -> Infer Type
updateAliasVars t args = do
  case t of
    TAlias _ _ vars t' ->
      let instArgs = M.fromList $ zip vars args

          update :: Type -> Infer Type
          update ty = case ty of
            TVar tv -> case M.lookup tv instArgs of
              Just x  -> return x
              Nothing -> newTVar Star --return ty --throwError $ InferError (UnboundVariable (ppShow tv)) NoReason 
            TApp l r -> do
              l' <- update l
              r' <- update r
              return $ TApp l' r'
            TCon _ -> return ty
            TTuple ts -> do
              ts' <- mapM update ts
              return $ TTuple ts'
            TRecord fs o -> do
              fs' <- mapM update fs
              return $ TRecord fs' o

      in  update t'

    _ -> return t
