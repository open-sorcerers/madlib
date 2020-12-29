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
      (TAlias _ _ _ t          ) -> return t
      t -> return t


typingToType env (Meta info area (Src.TRComp t ts)) = do
  params <- mapM (typingToType env) ts
  h   <- typingToType env (Meta info area $ Src.TRSingle t)
  return $ foldl TApp h params
  -- return head

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
