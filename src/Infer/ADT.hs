{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.ADT where

import qualified Data.Map                      as M
import           Control.Monad.Except
import           Data.Char                      ( isLower )

import           AST.Source
import           Infer.Type
import           Infer.Infer
import           Infer.Typing
import           Error.Error
import           Explain.Reason
import           Explain.Meta
import           Infer.Instantiate              ( newTVar )
import           Data.Maybe                     ( fromMaybe )
import           Text.Show.Pretty               ( ppShow )
import           Debug.Trace                    ( trace )
import           Data.List                      ( isInfixOf )


buildTypeDecls :: Env -> FilePath -> [TypeDecl] -> Infer TypeDecls
buildTypeDecls priorEnv astPath = buildTypeDecls' priorEnv astPath M.empty


buildTypeDecls' :: Env -> FilePath -> TypeDecls -> [TypeDecl] -> Infer TypeDecls
buildTypeDecls' _        _       _         []         = return M.empty
buildTypeDecls' priorEnv astPath typeDecls [typeDecl] = do
  (k, v) <- buildTypeDecl priorEnv astPath typeDecls typeDecl
  return $ M.singleton k v
buildTypeDecls' priorEnv astPath typeDecls (typeDecl : xs) = do
  a    <- buildTypeDecls' priorEnv astPath typeDecls [typeDecl]
  next <- buildTypeDecls' priorEnv astPath (M.union a typeDecls) xs
  return $ M.union a next


buildTypeDecl
  :: Env -> FilePath -> TypeDecls -> TypeDecl -> Infer (String, Type)
buildTypeDecl _ astPath typeDecls adt@ADT{} =
  case M.lookup (adtname adt) typeDecls of
    Just t  -> throwError $ InferError (ADTAlreadyDefined t) NoReason
    Nothing -> return
      ( adtname adt
      , TCon $ TC (adtname adt) (buildKind (length $ adtparams adt))
      )
buildTypeDecl priorEnv astPath typeDecls alias@Alias{} = do
  let name   = aliasname alias
  let params = (`TV` Star) <$> aliasparams alias
  let typing = aliastype alias
  typingType <- typingToType
    priorEnv { envtypes = M.union (envtypes priorEnv) typeDecls }
    typing
  return (name, TAlias astPath name params typingType)


resolveTypeDecls :: Env -> FilePath -> TypeDecls -> [TypeDecl] -> Infer Vars
resolveTypeDecls priorEnv astPath priorTypeDecls typeDecls =
  mergeVars <$> mapM (resolveTypeDecl priorEnv astPath priorTypeDecls) typeDecls
 where
  mergeVars []   = M.empty
  mergeVars vars = foldr1 M.union vars


resolveTypeDecl :: Env -> FilePath -> TypeDecls -> TypeDecl -> Infer Vars
resolveTypeDecl priorEnv astPath typeDecls adt@ADT{} =
  let name   = adtname adt
      ctors  = adtconstructors adt
      params = adtparams adt
  in  foldr1 M.union
        <$> mapM
              (resolveADTConstructor priorEnv astPath typeDecls name params)
              ctors
resolveTypeDecl _ _ _ Alias{} = return M.empty


resolveADTConstructor
  :: Env -> FilePath -> TypeDecls -> Name -> [Name] -> Constructor -> Infer Vars
resolveADTConstructor priorEnv astPath typeDecls n params (Constructor cname cparams)
  = do
    let gens = zip params (map TGen [0 ..])
    let rt =
          foldl TApp (TCon $ TC n (buildKind $ length params)) $ snd <$> gens
    t' <- mapM (argToType priorEnv gens typeDecls n params) cparams
    let ctype = foldr1 fn (t' <> [rt])
    let vars = M.fromList
          [(cname, Forall (replicate (countGens ctype) Star) ([] :=> ctype))]
    return vars

buildKind :: Int -> Kind
buildKind n | n > 0     = Kfun Star $ buildKind (n - 1)
            | otherwise = Star

countGens :: Type -> Int
countGens t = case t of
  TApp    l  r -> countGens l + countGens r
  TRecord fs _ -> sum $ countGens <$> M.elems fs
  TGen _       -> 1
  _            -> 0


argToType
  :: Env
  -> [(Name, Type)]
  -> TypeDecls
  -> Name
  -> [Name]
  -> Typing
  -> Infer Type
argToType _ gens typeDecls _ params (Meta _ _ (TRSingle n))
  | n == "Number" = return tNumber
  | n == "Boolean" = return tBool
  | n == "String" = return tStr
  | isLower (head n) = return
  $ fromMaybe (TGen 0) (M.lookup n (M.fromList gens))
  | otherwise = case M.lookup n typeDecls of
    Just a  -> return a
    Nothing -> throwError $ InferError (UnknownType n) NoReason

argToType priorEnv gens typeDecls name params (Meta _ _ (TRComp tname targs)) =
  case M.lookup tname (envtypes priorEnv <> typeDecls) of
    Just t@(TCon _) -> foldM
      (\prev a -> do
        arg <- argToType priorEnv gens typeDecls name params a
        return $ TApp prev arg
      )
      t
      targs
    Nothing -> throwError $ InferError (UnknownType tname) NoReason

argToType priorEnv gens typeDecls name params (Meta _ _ (TRArr l r)) = do
  l' <- argToType priorEnv gens typeDecls name params l
  r' <- argToType priorEnv gens typeDecls name params r
  return $ l' `fn` r'

argToType priorEnv gens typeDecls name params (Meta _ _ (TRRecord f)) = do
  f' <- mapM (argToType priorEnv gens typeDecls name params) f
  return $ TRecord f' False

argToType priorEnv gens typeDecls name params (Meta _ _ (TRTuple elems)) = do
  elems' <- mapM (argToType priorEnv gens typeDecls name params) elems
  let tupleT = getTupleCtor (length elems)
  return $ foldl TApp tupleT elems'
