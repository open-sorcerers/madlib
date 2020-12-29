{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Solve where

import qualified Data.Map                      as M
import qualified Data.Set                      as S
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Foldable                  ( foldrM )
import qualified Parse.AST                     as AST
import qualified AST.Source                    as Src
import qualified AST.Solved                    as Slv
import           Infer.Infer
import           Infer.Type
import           Infer.Env
import           Infer.Typing
import           Infer.Substitute
import           Infer.Unify
import           Infer.Instantiate
import           Error.Error
import           Explain.Reason
import           Explain.Meta
import           Explain.Location
import           Utils.Tuple
import           Data.List                      ( find )
import           Data.Maybe                     ( fromMaybe )
import           Debug.Trace                    ( trace )
import           Text.Show.Pretty               ( ppShow )
import           Infer.Scheme                   ( toScheme )
import qualified Utils.Tuple as T


infer :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
infer env lexp =
  let (Meta _ area exp) = lexp
  in  case exp of
        Src.LNum _ -> return (M.empty, tNumber, applyLitSolve lexp tNumber)
        Src.LStr _ -> return (M.empty, tStr, applyLitSolve lexp tStr)
        Src.LBool _ -> return (M.empty, tBool, applyLitSolve lexp tBool)
        Src.LUnit -> return (M.empty, tUnit, applyLitSolve lexp tUnit)

        Src.Var _              -> inferVar env lexp
        Src.Abs _ _            -> inferAbs env lexp
        Src.App _ _ _          -> inferApp env lexp
        Src.Assignment _ _     -> inferAssignment env lexp
        Src.Where      _ _     -> inferWhere env lexp
        Src.Record _           -> inferRecord env lexp
        Src.FieldAccess _ _    -> inferFieldAccess env lexp
        Src.TypedExp    _ _    -> inferTypedExp env lexp
        Src.ListConstructor  _ -> inferListConstructor env lexp
        Src.TupleConstructor _ -> inferTupleConstructor env lexp
        Src.Export           _ -> inferExport env lexp
        Src.If _ _ _           -> inferIf env lexp
        Src.JSExp c            -> do
          t <- newTVar Star
          return (M.empty, t, Slv.Solved t area (Slv.JSExp c))


applyLitSolve :: Src.Exp -> Type -> Slv.Exp
applyLitSolve (Meta _ area exp) t = case exp of
  Src.LNum  v -> Slv.Solved t area $ Slv.LNum v
  Src.LStr  v -> Slv.Solved t area $ Slv.LStr v
  Src.LBool v -> Slv.Solved t area $ Slv.LBool v
  Src.LUnit   -> Slv.Solved t area $ Slv.LUnit

applyAbsSolve :: Src.Exp -> Slv.Name -> [Slv.Exp] -> Type -> Slv.Exp
applyAbsSolve (Meta _ loc _) param body t =
  Slv.Solved t loc $ Slv.Abs param body

applyAssignmentSolve :: Src.Exp -> Slv.Name -> Slv.Exp -> Type -> Slv.Exp
applyAssignmentSolve (Meta _ loc _) n exp t =
  Slv.Solved t loc $ Slv.Assignment n exp


updateType :: Slv.Exp -> Type -> Slv.Exp
updateType (Slv.Solved _ a e) t' = Slv.Solved t' a e


updatePattern :: Src.Pattern -> Slv.Pattern
updatePattern (Meta _ _ pat) = case pat of
  Src.PVar name             -> Slv.PVar name
  Src.PAny                  -> Slv.PAny
  Src.PCtor name patterns   -> Slv.PCtor name (updatePattern <$> patterns)
  Src.PNum    n             -> Slv.PNum n
  Src.PStr    n             -> Slv.PStr n
  Src.PBool   n             -> Slv.PBool n
  Src.PCon    n             -> Slv.PCon n
  Src.PRecord fieldPatterns -> Slv.PRecord (updatePattern <$> fieldPatterns)
  Src.PList   patterns      -> Slv.PList (updatePattern <$> patterns)
  Src.PTuple  patterns      -> Slv.PTuple (updatePattern <$> patterns)
  Src.PSpread pat'          -> Slv.PSpread (updatePattern pat')


updateTyping :: Src.Typing -> Slv.Typing
updateTyping typing = case typing of
  Meta _ _ (Src.TRSingle name   ) -> Slv.TRSingle name

  Meta _ _ (Src.TRComp name vars) -> Slv.TRComp name (updateTyping <$> vars)

  Meta _ _ (Src.TRArr  l    r   ) -> Slv.TRArr (updateTyping l) (updateTyping r)

  Meta _ _ (Src.TRRecord fields ) -> Slv.TRRecord (updateTyping <$> fields)

  Meta _ _ (Src.TRTuple  elems  ) -> Slv.TRTuple (updateTyping <$> elems)



-- INFER VAR

inferVar :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferVar env exp@(Meta _ area (Src.Var n)) = case n of
  ('.' : name) -> do
    let s =
          Forall [Star]
            $   []
            :=> (TRecord (M.fromList [(name, TGen 0)]) True `fn` TGen 0)
    t <- instantiate s
    return (M.empty, qualType t, Slv.Solved (qualType t) area $ Slv.Var n)

  _ -> do
    sc         <- catchError (lookupVar env n) (enhanceVarError env exp area)
    (ps :=> t) <- instantiate sc
    return (M.empty, t, Slv.Solved t area $ Slv.Var n)

enhanceVarError :: Env -> Src.Exp -> Area -> InferError -> Infer Scheme
enhanceVarError env exp area (InferError e _) = throwError
  $ InferError e (Reason (VariableNotDeclared exp) (envcurrentpath env) area)



-- INFER ABSTRACTIONS

inferAbs :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferAbs env l@(Meta _ _ (Src.Abs param body)) = do
  tv <- newTVar Star
  let env' = extendVars env (param, Forall [] ([] :=> tv))
  (s1, t1, es) <- inferBody env' body
  let t = apply env s1 (tv `fn` t1)
  return (s1, t, applyAbsSolve l param es t)


inferBody :: Env -> [Src.Exp] -> Infer (Substitution, Type, [Slv.Exp])
inferBody env [exp   ] = (\(s, t, e) -> (s, t, [e])) <$> infer env exp

inferBody env (e : xs) = do
  (s, t, e') <- infer env e
  let exp = Slv.extractExp e'
  let env' = case exp of
        Slv.Assignment name _ ->
          extendVars env (name, Forall [kind t] ([] :=> t))

        Slv.TypedExp (Slv.Solved _ _ (Slv.Assignment name _)) _ ->
          extendVars env (name, Forall [kind t] ([] :=> t))

        _ -> env

  (\(sb, tb, eb) -> (compose env s sb, tb, e' : eb)) <$> inferBody env' xs


-- INFER APP

inferApp :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferApp env (Meta _ area (Src.App abs arg final)) = do
  tv             <- newTVar Star
  (s1, t1, eabs) <- infer env abs
  (s2, t2, earg) <- infer (apply env (removeRecordTypes s1) env) arg

  s3             <- case unify env (apply env s2 t1) (t2 `fn` tv) of
    Right s -> return s
    Left  e -> throwError $ InferError e $ Reason (WrongTypeApplied abs arg)
                                                  (envcurrentpath env)
                                                  (getArea arg)
  let t = apply env s3 tv

  let solved = Slv.Solved t area
        $ Slv.App eabs (updateType earg $ apply env s3 t2) final

  return (compose env s3 (compose env s2 s1), t, solved)


-- INFER ASSIGNMENT

inferAssignment :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferAssignment env e@(Meta _ _ (Src.Assignment name exp)) = do
  t <- newTVar Star
  let env' = extendVars env (name, Forall [] ([] :=> t))
  (s1, t1, e1) <- infer env' exp
  return (s1, t1, applyAssignmentSolve e name e1 t1)



-- INFER EXPORT

inferExport :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferExport env (Meta _ area (Src.Export exp)) = do
  (s, t, e) <- infer env exp
  return (s, t, Slv.Solved t area (Slv.Export e))



-- INFER LISTCONSTRUCTOR

inferListConstructor :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferListConstructor env (Meta _ area (Src.ListConstructor elems)) =
  case elems of
    [] -> do
      tv <- newTVar Star
      let t = TApp tList tv
      return (M.empty, t, Slv.Solved t area (Slv.ListConstructor []))

    elems -> do
      inferred <- mapM (inferListItem env) elems
      let (_, t1, _) = head inferred
      s <- unifyToInfer env $ unifyElems env (mid <$> inferred)
      let t          = TApp tList (apply env s t1)
      return (s, t, Slv.Solved t area (Slv.ListConstructor (lst <$> inferred)))


inferListItem :: Env -> Src.ListItem -> Infer (Substitution, Type, Slv.ListItem)
inferListItem env li = case li of
  Src.ListItem exp -> do
    (s, t, e) <- infer env exp
    return (s, t, Slv.ListItem e)

  Src.ListSpread exp -> do
    (s, t, e) <- infer env exp
    case t of
      TApp (TCon (TC "List" _)) t' -> return (s, t', Slv.ListSpread e)

      TVar _ -> return (s, t, Slv.ListSpread e)

      _ -> throwError $ InferError (WrongSpreadType $ show t) NoReason



-- INFER TUPLE CONSTRUCTOR

inferTupleConstructor :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferTupleConstructor env (Meta _ area (Src.TupleConstructor elems)) = do
  inferredElems <- mapM (infer env) elems
  let elemSubsts = beg <$> inferredElems
  let elemTypes  = mid <$> inferredElems
  let elemEXPS   = lst <$> inferredElems

  let s          = foldr (compose env) M.empty elemSubsts
  let t          = TTuple elemTypes

  return (s, t, Slv.Solved t area (Slv.TupleConstructor elemEXPS))



-- INFER RECORD

inferRecord :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferRecord env exp = do
  let Meta _ area (Src.Record fields) = exp

  inferred <- mapM (inferRecordField env) fields
  open     <- shouldBeOpen env fields
  let inferredFields = lst <$> inferred
      subst          = foldr (compose env) M.empty (beg <$> inferred)
      recordType     = TRecord (M.fromList $ concat $ mid <$> inferred) open
  return
    (subst, recordType, Slv.Solved recordType area (Slv.Record inferredFields))

inferRecordField
  :: Env -> Src.Field -> Infer (Substitution, [(Slv.Name, Type)], Slv.Field)
inferRecordField env field = case field of
  Src.Field (name, exp) -> do
    (s, t, e) <- infer env exp
    return (s, [(name, t)], Slv.Field (name, e))

  Src.FieldSpread exp -> do
    (s, t, e) <- infer env exp
    case t of
      TRecord tfields _ -> return (s, M.toList tfields, Slv.FieldSpread e)

      -- TODO: When we get here we should make it open !!
      TVar _ -> return (s, [], Slv.FieldSpread e)

      -- TODO: This needs to be a new error type maybe ?
      _ -> throwError $ InferError (WrongSpreadType $ show t) NoReason

shouldBeOpen :: Env -> [Src.Field] -> Infer Bool
shouldBeOpen env = foldrM
  (\field r -> case field of
    Src.Field       _ -> return $ False || r
    Src.FieldSpread e -> do
      (_, t, _) <- infer env e
      case t of
        TRecord _ _ -> return $ False || r
        TVar _      -> return $ True || r
  )
  False


-- INFER FIELD ACCESS

inferFieldAccess :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferFieldAccess env (Meta _ area (Src.FieldAccess rec@(Meta _ _ re) abs@(Meta _ _ (Src.Var ('.' : name)))))
  = do
    (fieldSubst , fieldType , fieldExp ) <- infer env abs
    (recordSubst, recordType, recordExp) <- infer env rec

    let foundFieldType = case recordType of
          TRecord fields _ -> M.lookup name fields
          _                -> Nothing

    case foundFieldType of
      Just t -> do
        t' <- instantiate $ Forall [kind t] ([] :=> t)
        let solved =
              Slv.Solved (qualType t') area (Slv.FieldAccess recordExp fieldExp)
        return (fieldSubst, qualType t', solved)

      Nothing -> case recordType of
        TRecord _ False ->
          throwError $ InferError (FieldNotExisting name) (AreaReason area)
        _ -> do
          tv <- newTVar Star
          s3 <-
            case
              unify env (apply env recordSubst fieldType) (recordType `fn` tv)
            of
              Right s -> return s
              Left  e -> throwError $ InferError e NoReason
          let s          = compose env s3 recordSubst
          let t          = apply env s tv

          let recordExp' = updateType recordExp (apply env s3 recordType)
          let solved = Slv.Solved t area (Slv.FieldAccess recordExp' fieldExp)

          return (s, t, solved)



-- INFER IF

inferIf :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferIf env exp@(Meta _ area (Src.If cond truthy falsy)) = do
  (s1, tcond  , econd  ) <- infer env cond
  (s2, ttruthy, etruthy) <- infer env truthy
  (s3, tfalsy , efalsy ) <- infer env falsy

  s4 <- catchError (unifyToInfer env $ unify env tBool tcond)
                   (addConditionReason env exp cond area)
  s5 <- catchError (unifyToInfer env $ unify env ttruthy tfalsy)
                   (addBranchReason env exp falsy area)

  let t = apply env s5 ttruthy

  return
    ( compose env s1 (compose env s2 (compose env s3 (compose env s4 s5)))
    , t
    , Slv.Solved t area (Slv.If econd etruthy efalsy)
    )

addConditionReason
  :: Env -> Src.Exp -> Src.Exp -> Area -> InferError -> Infer Substitution
addConditionReason env ifExp condExp area (InferError e _) =
  throwError $ InferError
    e
    (Reason (IfElseCondIsNotBool ifExp condExp) (envcurrentpath env) area)

addBranchReason
  :: Env -> Src.Exp -> Src.Exp -> Area -> InferError -> Infer Substitution
addBranchReason env ifExp falsyExp area (InferError e _) =
  throwError $ InferError
    e
    (Reason (IfElseBranchTypesDontMatch ifExp falsyExp)
            (envcurrentpath env)
            area
    )


-- INFER WHERE

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

    s <- case unifyElems (mergeVars env vars) ts of
      Right r -> return r
      Left e -> throwError $ InferError e NoReason

    return (ps, M.map (apply env s) vars, TTuple (apply env s ts))
  
  Src.PList pats -> do
    li <- mapM (inferPListItem env) pats
    let ts   = T.lst <$> li
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
  

inferWhere :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferWhere env (Meta _ area (Src.Where exp iss)) = do
  (s, t, e) <- infer env exp
  tv        <- newTVar Star
  pss       <- mapM (inferBranch env tv t) iss

  let issSubstitution = foldr1 (compose env) $ (beg <$> pss) <> [s]

  s' <- case unifyElems env (Slv.getType . lst <$> pss) of
    Left e -> throwError $ InferError e NoReason
    Right r -> return r

  let s'' = compose env s' issSubstitution

  let iss = (\(Slv.Solved t a is) -> Slv.Solved (apply env s'' t) a is) . lst <$> pss
  let wher = Slv.Solved (apply env s'' tv) area $ Slv.Where (updateType e (apply env s'' t)) iss
  return (s'', apply env s'' tv, (trace ("S'': "<>ppShow s''<>"\nTV: "<>ppShow tv<>"\nS: "<>ppShow s) wher))


inferBranch
  :: Env -> Type -> Type -> Src.Is -> Infer (Substitution, [Pred], Slv.Is)
inferBranch env tv t (Meta _ area (Src.Is pat exp)) = do
  (ps, vars, t') <- inferPattern env pat
  s              <- case unify (mergeVars env vars) t (removeSpread t') of
    Right r -> return r
    Left e -> throwError $ InferError e (Reason (PatternTypeError exp pat) (envcurrentpath env) area)
  (s', t'', e') <- infer (mergeVars env vars) exp
  s''           <- case unify (mergeVars env vars) tv t'' of
    Right r -> return r
    Left e -> throwError $ InferError e (Reason (PatternTypeError exp pat) (envcurrentpath env) area)
  let t''' = extendRecord (s <> s'' <> s') t'
  s''' <- case unify (mergeVars env vars) t t''' of
    Right r -> return r
    Left e -> throwError $ InferError e (Reason (PatternTypeError exp pat) (envcurrentpath env) area)
  let subst = compose env (compose env (compose env s s') s'') s'''
  
  return
    ( trace ("EXT-ENV: "<>ppShow (mergeVars env vars)<>"\nS''': "<>ppShow s''') subst
    , ps
    , Slv.Solved (apply env subst (t''' `fn` t'')) area
      $ Slv.Is (updatePattern pat) (updateType e' (apply env subst t''))
    )

removeSpread :: Type -> Type
removeSpread t = case t of
  TRecord fs o -> TRecord (M.filterWithKey (\k _ -> k /= "...") fs) o
  _ -> t

extendRecord :: Substitution -> Type -> Type
extendRecord s t = case t of
  TRecord fs _ ->
    let spread = M.lookup "..." (trace ("S: "<>ppShow s<>"\nT: "<>ppShow t) fs)
        fs'    = M.map (extendRecord s) fs
    in case spread of
      Just (TVar tv) -> case M.lookup tv s of
        Just t' -> do
          case extendRecord s t' of
            TRecord fs'' _ -> TRecord (M.filterWithKey (\k _ -> k /= "...") (fs' <> fs'')) True
            _ -> t
        _ -> t
      _ -> t

  _ -> t



-- INFER TYPEDEXP

inferTypedExp :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferTypedExp env (Meta _ area (Src.TypedExp exp typing)) = do
  t            <- typingToType env typing

  t'           <- instantiate $ Forall [kind t] ([] :=> t)

  (s1, t1, e1) <- infer env exp
  s2           <- case unify env (qualType t') t1 of
    Right solved -> return solved

    Left  err    -> throwError $ InferError
      err
      (Reason (TypeAndTypingMismatch exp typing (qualType t') t1)
              (envcurrentpath env)
              area
      )

  return
    ( compose env s1 s2
    , qualType t'
    , Slv.Solved
      (qualType t')
      area
      (Slv.TypedExp (updateType e1 (qualType t')) (updateTyping typing))
    )



inferExps :: Env -> [Src.Exp] -> Infer [Slv.Exp]
inferExps _   []       = return []

inferExps env [exp   ] = (: []) . lst <$> infer env exp

inferExps env (e : xs) = do
  (_, t, e') <- infer env e
  let exp = Slv.extractExp e'
  let
    env' = case exp of
      Slv.Assignment name _ ->
        extendVars env (name, Forall [kind t] ([] :=> t))

      Slv.TypedExp (Slv.Solved _ _ (Slv.Assignment name _)) _ ->
        extendVars env (name, Forall [kind t] ([] :=> t))

      Slv.TypedExp (Slv.Solved _ _ (Slv.Export (Slv.Solved _ _ (Slv.Assignment name _)))) _
        -> extendVars env (name, Forall [kind t] ([] :=> t))

      Slv.Export (Slv.Solved _ _ (Slv.Assignment name _)) ->
        extendVars env (name, Forall [kind t] ([] :=> t))

      _ -> env

  (e' :) <$> inferExps env' xs



solveTable :: Src.Table -> Src.AST -> Infer Slv.Table
solveTable table ast = do
  (table, _) <- solveTable' table ast
  return table

solveTable' :: Src.Table -> Src.AST -> Infer (Slv.Table, Env)
solveTable' table ast@Src.AST { Src.aimports } = do
  -- First we resolve imports to update the env
  (inferredASTs, adts, vars) <- solveImports table aimports

  let importEnv = Env { envtypes       = adts
                      , envvars        = vars
                      , envinterfaces  = []
                      , envinstances   = []
                      , envcurrentpath = fromMaybe "" (Src.apath ast)
                      }
  -- Then we infer the ast
  env <- buildInitialEnv importEnv ast
  let envWithImports = env { envtypes   = M.union (envtypes env) adts
                           , envvars    = M.union (envvars env) vars
                           }

  inferredAST <- inferAST envWithImports ast

  case Slv.apath inferredAST of
    Just fp -> return $ (M.insert fp inferredAST inferredASTs, envWithImports)



exportedExps :: Slv.AST -> Infer [(Slv.Name, Slv.Exp)]
exportedExps Slv.AST { Slv.aexps, Slv.apath } = case apath of
  Just p -> mapM (bundleExports p) $ filter isExport aexps

 where
  bundleExports _ exp = return $ case exp of
    e'@(Slv.Solved _ _ (Slv.Export (Slv.Solved _ _ (Slv.Assignment n _)))) ->
      (n, e')
    e'@(Slv.Solved _ _ (Slv.TypedExp (Slv.Solved _ _ (Slv.Export (Slv.Solved _ _ (Slv.Assignment n _)))) _))
      -> (n, e')

  isExport :: Slv.Exp -> Bool
  isExport a = case a of
    (Slv.Solved _ _ (Slv.Export _)) -> True
    (Slv.Solved _ _ (Slv.TypedExp (Slv.Solved _ _ (Slv.Export _)) _)) -> True

    _                               -> False


exportedADTs :: Slv.AST -> [Slv.Name]
exportedADTs Slv.AST { Slv.atypedecls } =
  Slv.adtName <$> filter Slv.adtExported atypedecls


solveImports
  :: Src.Table -> [Src.Import] -> Infer (Slv.Table, TypeDecls, Vars)
solveImports table (imp : is) = do
  let modulePath = Src.getImportAbsolutePath imp


  (solvedAST, solvedTable, envADTs, envSolved) <-
    case AST.findAST table modulePath of
      Right ast -> do
        (solvedTable, env) <- solveTable' table ast
        solvedAST          <- case M.lookup modulePath solvedTable of
          Just a -> return a
          Nothing ->
            throwError $ InferError (ImportNotFound modulePath) NoReason
        return (solvedAST, solvedTable, envtypes env, env)

      Left e -> throwError e

  exportedExps <- M.fromList <$> exportedExps solvedAST
  let exportedTypes    = mapM (return . Slv.getType) exportedExps

  let exportedADTNames = exportedADTs solvedAST
  let adtExports = M.filterWithKey (\k _ -> elem k exportedADTNames) envADTs

  let exportedConstructorNames = Slv.getConstructorName <$> concat
        (Slv.adtconstructors <$> filter (\x -> isADT x && Slv.adtExported x)
                                        (Slv.atypedecls solvedAST)
        )
  let buildConstructorVars = M.filterWithKey
        (\k v -> k `elem` exportedConstructorNames)
        (envvars envSolved)

  (exports, vars) <- case (exportedTypes, imp) of
    (Just exports, Meta _ _ (Src.DefaultImport namespace _ _)) -> do
      constructorVars <- mapM instantiate buildConstructorVars
      let cvNames  = M.keys constructorVars
      let cvQs     = snd <$> M.toList constructorVars
      let (ps, ts) = extractQualifiers cvQs


      return
        ( M.fromList [(namespace, TRecord exports False)]
        , M.fromList
          [ ( namespace
            , Forall []
            $   ps
            :=> (TRecord (M.union exports (M.fromList (zip cvNames ts))) False)
            )
          ]
        )

    (Just exports, _) -> return (exports, buildConstructorVars)

    (Nothing, _) ->
      throwError $ InferError (ImportNotFound modulePath) NoReason


  (nextTable, nextADTs, nextVars) <- solveImports table is

  mergedADTs <- do
    adtExports <- if M.intersection adtExports nextADTs == M.empty
      then return $ M.union adtExports nextADTs
      else throwError $ InferError FatalError NoReason
    case imp of
      Meta _ _ (Src.DefaultImport namespace _ absPath) -> return
        $ M.mapKeys (mergeTypeDecl namespace absPath adtExports) adtExports

      _ -> return adtExports


  return
    ( M.insert modulePath solvedAST (M.union solvedTable nextTable)
    , mergedADTs
    , M.union nextVars vars
    )

solveImports _ [] = return
  (M.empty, envtypes initialEnv, envvars initialEnv)

isADT :: Slv.TypeDecl -> Bool
isADT Slv.ADT{} = True
isADT _         = False

mergeTypeDecl :: String -> FilePath -> M.Map String Type -> String -> String
mergeTypeDecl namespace absPath adts key = case M.lookup key adts of
  Just (TComp path _ _) ->
    if path == absPath then namespace <> "." <> key else key
  Just (TAlias path _ _ _) ->
    if path == absPath then namespace <> "." <> key else key
  _ -> key


updateInterface :: Src.Interface -> Slv.Interface
updateInterface (Src.Interface name var methods) =
  Slv.Interface name var (updateTyping <$> methods)

inferAST :: Env -> Src.AST -> Infer Slv.AST
inferAST env Src.AST { Src.aexps, Src.apath, Src.aimports, Src.atypedecls, Src.ainstances, Src.ainterfaces }
  = do
    inferredExps      <- inferExps env aexps
    inferredInstances <- mapM (resolveInstance env) ainstances
    let updatedInterfaces = updateInterface <$> ainterfaces

    return Slv.AST { Slv.aexps       = inferredExps
                   , Slv.apath       = apath
                   , Slv.atypedecls  = updateADT <$> atypedecls
                   , Slv.aimports    = updateImport <$> aimports
                   , Slv.ainterfaces = updatedInterfaces
                   , Slv.ainstances  = inferredInstances
                   }

resolveInstance :: Env -> Src.Instance -> Infer Slv.Instance
resolveInstance env (Src.Instance interface ty dict) = do
  dict' <- mapM (infer env) dict
  let dict'' = M.map lst dict'
  return $ Slv.Instance interface (updateTyping ty) dict''

updateImport :: Src.Import -> Slv.Import
updateImport i = case i of
  Meta _ _ (Src.NamedImport   ns p fp) -> Slv.NamedImport ns p fp

  Meta _ _ (Src.DefaultImport n  p fp) -> Slv.DefaultImport n p fp


updateADT :: Src.TypeDecl -> Slv.TypeDecl
updateADT adt@Src.ADT{} =
  let name     = Src.adtname adt
      params   = Src.adtparams adt
      ctors    = Src.adtconstructors adt
      exported = Src.adtexported adt
  in  Slv.ADT { Slv.adtname         = name
              , Slv.adtparams       = params
              , Slv.adtconstructors = updateADTConstructor <$> ctors
              , Slv.adtexported     = exported
              }
updateADT alias@Src.Alias{} =
  let name     = Src.aliasname alias
      params   = Src.aliasparams alias
      t        = Src.aliastype alias
      exported = Src.aliasexported alias
  in  Slv.Alias { Slv.aliasname     = name
                , Slv.aliasparams   = params
                , Slv.aliastype     = updateTyping t
                , Slv.aliasexported = exported
                }

updateADTConstructor :: Src.Constructor -> Slv.Constructor
updateADTConstructor (Src.Constructor cname cparams) =
  Slv.Constructor cname $ updateTyping <$> cparams

-- TODO: Should get rid of that and handle the Either correctly where it is called
unifyToInfer :: Env -> Either TypeError Substitution -> Infer Substitution
unifyToInfer _ u = case u of
  Right s -> return s
  Left  e -> throwError $ InferError e NoReason


-- -- TODO: Make it call inferAST so that inferAST can return an (Infer TBD)
-- -- Well, or just adapt it somehow
runInfer :: Env -> Src.AST -> Either InferError Slv.AST
runInfer env ast =
  fst <$> runExcept (runStateT (inferAST env ast) Unique { count = 0 })

