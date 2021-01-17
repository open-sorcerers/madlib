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
import           Infer.Scheme                   ( quantify )
import           Debug.Trace                    ( trace )
import           Text.Show.Pretty               ( ppShow )
import           Infer.Instantiate              ( newTVar )
import qualified Data.Set as S
import Data.List (nub, union)


typingToScheme :: Env -> Src.Typing -> Infer Scheme
typingToScheme env typing = do
  (ps :=> t) <- qualTypingToQualType env typing
  let vars = S.toList $ S.fromList $ collectVars (trace ("TYPING T: "<>ppShow t) t) <> concat (collectPredVars <$> ps)
  return $ quantify vars (ps :=> t)


qualTypingToQualType :: Env -> Src.Typing -> Infer (Qual Type)
qualTypingToQualType env t@(Meta _ _ typing) = case typing of
  Src.TRConstrained constraints typing' -> do
    t  <- typingToType env typing'
    ps <- mapM (constraintToPredicate env t) constraints
    return $ ps :=> t

  _ -> ([] :=>) <$> typingToType env t


constraintToPredicate :: Env -> Type -> Src.Typing -> Infer Pred
constraintToPredicate env t (Meta _ _ (Src.TRComp n [Meta _ _ (Src.TRSingle var)])) =
  case searchVarInType var t of
    Just v -> return $ IsIn n [v]
    -- Nothing -> throwError $ ...


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
      (TAlias _ _ _ t) -> updateAliasVars h []
      t                -> return t


typingToType env (Meta info area (Src.TRComp t ts)) 
  | isLower . head $ t = do
      params <- mapM (typingToType env) ts
      return $ foldl TApp (TVar $ TV t (buildKind (length ts))) params
  | otherwise = do
      h      <- lookupADT env t
      params <- mapM (typingToType env) ts
      case h of
        (TAlias _ _ _ t) -> updateAliasVars h params
        t                -> return $ foldl TApp t params


typingToType env (Meta _ _ (Src.TRArr l r)) = do
  l' <- typingToType env l
  r' <- typingToType env r
  return $ l' `fn` r'

typingToType env (Meta _ _ (Src.TRRecord fields)) = do
  fields' <- mapM (typingToType env) fields
  return $ TRecord fields' False

typingToType env (Meta _ _ (Src.TRTuple elems)) = do
  elems' <- mapM (typingToType env) elems
  let tupleT = getTupleCtor (length elems)
  return $ foldl TApp tupleT elems'

lookupADT :: Env -> String -> Infer Type
lookupADT env x = do
  case M.lookup x $ envtypes env of
    Nothing -> throwError $ InferError (UnknownType x) NoReason
    Just x  -> return x


collectQualTypeVars :: Qual Type -> [TVar]
collectQualTypeVars (ps :=> t) =
  S.toList $ S.fromList $ collectVars t ++ concat (collectPredVars <$> ps)


collectVars :: Type -> [TVar]
collectVars t = case t of
  TVar tv      -> [tv]
  TApp    l  r -> collectVars l `union` collectVars r
  TRecord fs _ -> nub $ concat $ collectVars <$> M.elems fs
  _            -> []


collectPredVars :: Pred -> [TVar]
collectPredVars (IsIn _ ts) = nub $ concat $ collectVars <$> ts


updateAliasVars :: Type -> [Type] -> Infer Type
updateAliasVars t args = do
  case t of
    TAlias _ _ vars t' ->
      let instArgs = M.fromList $ zip vars args

          update :: Type -> Infer Type
          update ty = case ty of
            TVar tv -> case M.lookup tv instArgs of
              Just x  -> return x
              Nothing -> return ty
            TApp l r -> do
              l' <- update l
              r' <- update r
              return $ TApp l' r'
            TCon _       -> return ty
            TRecord fs o -> do
              fs' <- mapM update fs
              return $ TRecord fs' o
      in  update t'

    _ -> return t
