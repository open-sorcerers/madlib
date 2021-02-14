{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
module Canonicalize.Canonicalize where

import qualified Data.Map                      as M
import qualified AST.Canonical                 as Can
import qualified AST.Source                    as Src
import           Infer.Type
import           Data.List
import           Explain.Meta
import           Control.Monad.Except
import           Error.Error
import           Explain.Reason


type CanonicalM a = forall m . MonadError InferError m => m a


class Canonicalizable a b where
  canonicalize :: a -> CanonicalM b


instance Canonicalizable Src.Exp Can.Exp where
  canonicalize (Src.Source infos area e) = case e of
    Src.LNum  x           -> return $ Can.Canonical area (Can.LNum x)

    Src.LStr  x           -> return $ Can.Canonical area (Can.LStr x)

    Src.LBool x           -> return $ Can.Canonical area (Can.LBool x)

    Src.LUnit             -> return $ Can.Canonical area Can.LUnit

    Src.TemplateString es -> do
      es' <- mapM canonicalize es
      return $ Can.Canonical area (Can.TemplateString es')

    Src.JSExp js         -> return $ Can.Canonical area (Can.JSExp js)

    Src.App fn arg close -> do
      fn'  <- canonicalize fn
      arg' <- canonicalize arg
      return $ Can.Canonical area (Can.App fn' arg' close)

    Src.FieldAccess rec field -> do
      rec'   <- canonicalize rec
      field' <- canonicalize field
      return $ Can.Canonical area (Can.FieldAccess rec' field')

    Src.NamespaceAccess n ->
      return $ Can.Canonical area (Can.NamespaceAccess n)

    Src.Abs param body -> do
      body' <- mapM canonicalize body
      return $ Can.Canonical area (Can.Abs param body')

    Src.Assignment name exp -> do
      exp' <- canonicalize exp
      return $ Can.Canonical area (Can.Assignment name exp')

    Src.Export exp -> do
      exp' <- canonicalize exp
      return $ Can.Canonical area (Can.Export exp')

    Src.Var name            -> return $ Can.Canonical area (Can.Var name)

    Src.TypedExp exp typing -> do
      exp'    <- canonicalize exp
      typing' <- canonicalize typing
      return $ Can.Canonical area (Can.TypedExp exp' typing')

    Src.ListConstructor items -> do
      items' <- mapM canonicalize items
      return $ Can.Canonical area (Can.ListConstructor items')

    Src.TupleConstructor exps -> do
      exps' <- mapM canonicalize exps
      return $ Can.Canonical area (Can.TupleConstructor exps')

    Src.Record fields -> do
      fields' <- mapM canonicalize fields
      return $ Can.Canonical area (Can.Record fields')

    Src.If cond truthy falsy -> do
      cond'   <- canonicalize cond
      truthy' <- canonicalize truthy
      falsy'  <- canonicalize falsy
      return $ Can.Canonical area (Can.If cond' truthy' falsy')

    Src.Where exp iss -> do
      exp' <- canonicalize exp
      iss' <- mapM canonicalize iss
      return $ Can.Canonical area (Can.Where exp' iss')


instance Canonicalizable Src.Typing Can.Typing where
  canonicalize (Src.Source _ area t) = case t of
    Src.TRSingle name       -> return $ Can.Canonical area (Can.TRSingle name)

    Src.TRComp name typings -> do
      typings' <- mapM canonicalize typings
      return $ Can.Canonical area (Can.TRComp name typings')

    Src.TRArr left right -> do
      left'  <- canonicalize left
      right' <- canonicalize right
      return $ Can.Canonical area (Can.TRArr left' right')

    Src.TRRecord fields -> do
      fields' <- mapM canonicalize fields
      return $ Can.Canonical area (Can.TRRecord fields')

    Src.TRTuple typings -> do
      typings' <- mapM canonicalize typings
      return $ Can.Canonical area (Can.TRTuple typings')

    Src.TRConstrained constraints typing -> do
      constraints' <- mapM canonicalize constraints
      typing'      <- canonicalize typing
      return $ Can.Canonical area (Can.TRConstrained constraints' typing')

instance Canonicalizable Src.ListItem Can.ListItem where
  canonicalize item = case item of
    Src.ListItem exp -> do
      exp' <- canonicalize exp
      return $ Can.ListItem exp'

    Src.ListSpread exp -> do
      exp' <- canonicalize exp
      return $ Can.ListSpread exp'

instance Canonicalizable Src.Field Can.Field where
  canonicalize item = case item of
    Src.Field (name, exp) -> do
      exp' <- canonicalize exp
      return $ Can.Field (name, exp')

    Src.FieldSpread exp -> do
      exp' <- canonicalize exp
      return $ Can.FieldSpread exp'

instance Canonicalizable Src.Is Can.Is where
  canonicalize (Src.Source _ area (Src.Is pat exp)) = do
    pat' <- canonicalize pat
    exp' <- canonicalize exp
    return $ Can.Canonical area (Can.Is pat' exp')

instance Canonicalizable Src.Pattern Can.Pattern where
  canonicalize (Src.Source _ area pat) = case pat of
    Src.PVar name       -> return $ Can.Canonical area (Can.PVar name)

    Src.PAny            -> return $ Can.Canonical area (Can.PAny)

    Src.PCtor name pats -> do
      pats' <- mapM canonicalize pats
      return $ Can.Canonical area (Can.PCtor name pats')

    Src.PNum    num  -> return $ Can.Canonical area (Can.PNum num)

    Src.PStr    str  -> return $ Can.Canonical area (Can.PStr str)

    Src.PBool   boo  -> return $ Can.Canonical area (Can.PBool boo)

    Src.PCon    name -> return $ Can.Canonical area (Can.PCon name)

    Src.PRecord pats -> do
      pats' <- mapM canonicalize pats
      return $ Can.Canonical area (Can.PRecord pats')

    Src.PList pats -> do
      pats' <- mapM canonicalize pats
      return $ Can.Canonical area (Can.PList pats')

    Src.PTuple pats -> do
      pats' <- mapM canonicalize pats
      return $ Can.Canonical area (Can.PTuple pats')

    Src.PSpread pat -> do
      pat' <- canonicalize pat
      return $ Can.Canonical area (Can.PSpread pat')

instance Canonicalizable Src.TypeDecl Can.TypeDecl where
  canonicalize typeDecl = case typeDecl of
    adt@Src.ADT{} -> do
      ctors <- mapM optimizeConstructors $ Src.adtconstructors adt
      return Can.ADT { Can.adtname         = Src.adtname adt
                     , Can.adtparams       = Src.adtparams adt
                     , Can.adtconstructors = ctors
                     , Can.adtexported     = Src.adtexported adt
                     }

    alias@Src.Alias{} -> do
      aliastype <- canonicalize $ Src.aliastype alias
      return Can.Alias { Can.aliasname     = Src.aliasname alias
                       , Can.aliasparams   = Src.aliasparams alias
                       , Can.aliastype     = aliastype
                       , Can.aliasexported = Src.aliasexported alias
                       }
   where
    optimizeConstructors :: Src.Constructor -> CanonicalM Can.Constructor
    optimizeConstructors (Src.Constructor name typings) = do
      typings' <- mapM canonicalize typings
      return $ Can.Constructor name typings'


instance Canonicalizable Src.Interface Can.Interface where
  canonicalize (Src.Interface constraints name vars methods) = do
    constraints' <- mapM canonicalize constraints
    methods'     <- mapM canonicalize methods
    return $ Can.Interface constraints' name vars methods'

instance Canonicalizable Src.Instance Can.Instance where
  canonicalize (Src.Instance constraints interface typings methods) = do
    constraints' <- mapM canonicalize constraints
    typings'     <- mapM canonicalize typings
    methods'     <- mapM canonicalize methods
    return $ Can.Instance constraints' interface typings' methods'

instance Canonicalizable Src.Import Can.Import where
  canonicalize (Src.Source _ area imp) = case imp of
    Src.NamedImport names relPath absPath ->
      return $ Can.Canonical area (Can.NamedImport names relPath absPath)

    Src.DefaultImport namespace relPath absPath ->
      return $ Can.Canonical area (Can.DefaultImport namespace relPath absPath)

instance Canonicalizable Src.AST Can.AST where
  canonicalize ast = do
    imports    <- mapM canonicalize $ Src.aimports ast
    exps       <- mapM canonicalize $ Src.aexps ast
    typeDecls  <- mapM canonicalize $ Src.atypedecls ast
    interfaces <- mapM canonicalize $ Src.ainterfaces ast
    instances  <- mapM canonicalize $ Src.ainstances ast

    return $ Can.AST { Can.aimports    = imports
                     , Can.aexps       = exps
                     , Can.atypedecls  = typeDecls
                     , Can.ainterfaces = interfaces
                     , Can.ainstances  = instances
                     , Can.apath       = Src.apath ast
                     }


canonicalizeTable :: Src.Table -> Either InferError Can.Table
canonicalizeTable table = runExcept $ mapM canonicalize table

findAST :: Can.Table -> FilePath -> Either InferError Can.AST
findAST table path = case M.lookup path table of
  Just found -> return found
  Nothing    -> Left $ InferError (ImportNotFound path) NoReason
