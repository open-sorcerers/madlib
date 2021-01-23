{-# LANGUAGE LambdaCase #-}
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
import           Data.Foldable                  (foldlM,  foldrM )
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
import           Data.List                      (intersect, (\\), union, partition,  find )
import           Data.Maybe                     ( fromMaybe )
import           Debug.Trace                    ( trace )
import           Text.Show.Pretty               ( ppShow )
import           Infer.Scheme                   ( quantify
                                                , toScheme
                                                )
import qualified Utils.Tuple                   as T
import           Infer.Pattern
import Infer.Pred


infer :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
infer env lexp = do
  let (Meta _ area exp) = lexp
  r@(s, ps, t, e) <- case exp of
    Src.LNum _ -> return (M.empty, [], tNumber, applyLitSolve lexp tNumber)
    Src.LStr _ -> return (M.empty, [], tStr, applyLitSolve lexp tStr)
    Src.LBool _ -> return (M.empty, [], tBool, applyLitSolve lexp tBool)
    Src.LUnit -> return (M.empty, [], tUnit, applyLitSolve lexp tUnit)

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
      return (M.empty, [], t, Slv.Solved t area (Slv.JSExp c))

  return r


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

  Meta _ _ (Src.TRConstrained ts t) -> Slv.TRConstrained (updateTyping <$> ts) (updateTyping t)



-- INFER VAR

inferVar :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferVar env exp@(Meta _ area (Src.Var n)) = case n of
  ('.' : name) -> do
    let s =
          Forall [Star]
            $   []
            :=> (TRecord (M.fromList [(name, TGen 0)]) True `fn` TGen 0)
    (ps :=> t) <- instantiate s
    return (M.empty, ps, t, Slv.Solved t area $ Slv.Var n)

  _ -> do
    sc         <- catchError (lookupVar env n) (enhanceVarError env exp area)
    (ps :=> t) <- instantiate sc

    let e = Slv.Solved t area $ Slv.Var n
    let e' = insertVarPlaceholders env e ps

    return (M.empty, ps, t, e')

enhanceVarError :: Env -> Src.Exp -> Area -> InferError -> Infer Scheme
enhanceVarError env exp area (InferError e _) = throwError
  $ InferError e (Reason (VariableNotDeclared exp) (envcurrentpath env) area)


insertVarPlaceholders :: Env -> Slv.Exp -> [Pred] -> Slv.Exp
insertVarPlaceholders _ exp [] = exp

insertVarPlaceholders env exp@(Slv.Solved t a e) (p:ps) =
  if isMethod env exp
    then case e of
      Slv.Var n -> Slv.Solved t a $ Slv.Placeholder (Slv.MethodRef (predClass p) n, predType p) exp
      _ -> exp
    else
      let exp' = case predType p of
            TVar _ -> Slv.Solved t a $ Slv.Placeholder (Slv.ClassRef (predClass p), predType p) exp
            _ -> exp
      in insertVarPlaceholders env exp' ps



-- INFER ABSTRACTIONS

inferAbs :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferAbs env l@(Meta _ _ (Src.Abs param body)) = do
  tv <- newTVar Star
  let env' = extendVars env (param, Forall [] ([] :=> tv))
  (s1, ps, t1, es) <- inferBody env' body
  let t = apply s1 (tv `fn` t1)
  return (s1, ps, t, applyAbsSolve l param es t)


inferBody :: Env -> [Src.Exp] -> Infer (Substitution, [Pred], Type, [Slv.Exp])
inferBody env [exp   ] = (\(s, ps, t, e) -> (s, ps, t, [e])) <$> infer env exp

inferBody env (e : xs) = do
  (s, ps, t, e') <- infer env e
  let exp = Slv.extractExp e'
  let env' = case exp of
        Slv.Assignment name _ ->
          extendVars env (name, Forall [kind t] (ps :=> t))

        Slv.TypedExp (Slv.Solved _ _ (Slv.Assignment name _)) _ ->
          extendVars env (name, Forall [kind t] (ps :=> t))

        _ -> env

  (\(sb, ps, tb, eb) -> (s `compose` sb, ps, tb, e' : eb)) <$> inferBody env' xs


-- INFER APP

inferApp :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferApp env (Meta _ area (Src.App abs arg final)) = do
  tv                  <- newTVar Star
  (s1, ps1, t1, eabs) <- infer env abs
  (s2, ps2, t2, earg) <- infer (apply (removeRecordTypes s1) env) arg

  s3             <- catchError (unify (apply s2 t1) (t2 `fn` tv)) (\case
        InferError (UnificationError _ _) _ ->
          throwError
            $ InferError (UnificationError (apply s2 t1) (t2 `fn` tv))
            $ Reason (WrongTypeApplied abs arg) (envcurrentpath env) (getArea arg)
        InferError e _ ->
          throwError
            $ InferError e
            $ Reason (WrongTypeApplied abs arg) (envcurrentpath env) (getArea arg)
    )

  let t = apply s3 tv

  let solved = Slv.Solved t area
        $ Slv.App eabs (updateType earg $ apply s3 t2) final

  return (s3 `compose` s2 `compose` s1, ps1 ++ ps2, t, solved)


-- INFER ASSIGNMENT

inferAssignment :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferAssignment env e@(Meta _ _ (Src.Assignment name exp)) = do
  t <- newTVar Star
  let env' = extendVars env (name, Forall [] ([] :=> t))
  (s1, ps1, t1, e1) <- infer env' exp
  return (s1, ps1, t1, applyAssignmentSolve e name e1 t1)



-- INFER EXPORT

inferExport :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferExport env (Meta _ area (Src.Export exp)) = do
  (s, ps, t, e) <- infer env exp
  return (s, ps, t, Slv.Solved t area (Slv.Export e))



-- INFER LISTCONSTRUCTOR

inferListConstructor :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferListConstructor env (Meta _ area (Src.ListConstructor elems)) =
  case elems of
    [] -> do
      tv <- newTVar Star
      let t = TApp tList tv
      return (M.empty, [], t, Slv.Solved t area (Slv.ListConstructor []))

    elems -> do
      inferred <- mapM (inferListItem env) elems
      let (_, _, t1, _) = head inferred
      s <- unifyElems env ((\(_, _, t, _) -> t) <$> inferred)
      let s' = foldr (<>) M.empty ((\(s, _, _, _) -> s) <$> inferred)
      let t = TApp tList (apply s t1)
      return (s `compose` s', [], t, Slv.Solved t area (Slv.ListConstructor ((\(_, _, _, es) -> es) <$> inferred)))


inferListItem :: Env -> Src.ListItem -> Infer (Substitution, [Pred], Type, Slv.ListItem)
inferListItem env li = case li of
  Src.ListItem exp -> do
    (s, ps, t, e) <- infer env exp
    return (s, ps, t, Slv.ListItem e)

  Src.ListSpread exp -> do
    (s, ps, t, e) <- infer env exp
    case t of
      TApp (TCon (TC "List" _)) t' -> return (s, ps, t', Slv.ListSpread e)

      TVar _ -> return (s, ps, t, Slv.ListSpread e)

      _ -> throwError $ InferError (WrongSpreadType $ show t) NoReason



-- INFER TUPLE CONSTRUCTOR

inferTupleConstructor :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferTupleConstructor env (Meta _ area (Src.TupleConstructor elems)) = do
  inferredElems <- mapM (infer env) elems
  let elemSubsts = (\(s, _, _, _) -> s) <$> inferredElems
  let elemTypes  = (\(_, _, t, _) -> t) <$> inferredElems
  let elemEXPS   = (\(_, _, _, es) -> es) <$> inferredElems

  let s          = foldr compose M.empty elemSubsts

  let tupleT     = getTupleCtor (length elems)
  let t          = foldl TApp tupleT elemTypes

  return (s, [], t, Slv.Solved t area (Slv.TupleConstructor elemEXPS))



-- INFER RECORD

inferRecord :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferRecord env exp = do
  let Meta _ area (Src.Record fields) = exp

  inferred <- mapM (inferRecordField env) fields
  open     <- shouldBeOpen env fields
  let inferredFields = lst <$> inferred
      subst          = foldr compose M.empty (beg <$> inferred)
      recordType     = TRecord (M.fromList $ concat $ mid <$> inferred) open
  return
    (subst, [], recordType, Slv.Solved recordType area (Slv.Record inferredFields))

inferRecordField
  :: Env -> Src.Field -> Infer (Substitution, [(Slv.Name, Type)], Slv.Field)
inferRecordField env field = case field of
  Src.Field (name, exp) -> do
    (s, ps, t, e) <- infer env exp
    return (s, [(name, t)], Slv.Field (name, e))

  Src.FieldSpread exp -> do
    (s, ps, t, e) <- infer env exp
    case t of
      TRecord tfields _ -> return (s, M.toList tfields, Slv.FieldSpread e)

      TVar _ -> return (s, [], Slv.FieldSpread e)

      _ -> throwError $ InferError (WrongSpreadType $ show t) NoReason

shouldBeOpen :: Env -> [Src.Field] -> Infer Bool
shouldBeOpen env = foldrM
  (\field r -> case field of
    Src.Field       _ -> return r
    Src.FieldSpread e -> do
      (_, _, t, _) <- infer env e
      case t of
        TRecord _ _ -> return r
        TVar _      -> return True
  )
  False


-- INFER FIELD ACCESS

inferFieldAccess :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferFieldAccess env (Meta _ area (Src.FieldAccess rec@(Meta _ _ re) abs@(Meta _ _ (Src.Var ('.' : name)))))
  = do
    (fieldSubst , fieldPs, fieldType , fieldExp )  <- infer env abs
    (recordSubst, recordPs, recordType, recordExp) <- infer env rec

    let foundFieldType = case recordType of
          TRecord fields _ -> M.lookup name fields
          _                -> Nothing

    case foundFieldType of
      Just t -> do
        (ps :=> t') <- instantiate $ Forall [kind t] ([] :=> t)
        let solved =
              Slv.Solved t' area (Slv.FieldAccess recordExp fieldExp)
        return (fieldSubst, ps, t', solved)

      Nothing -> case recordType of
        TRecord _ False ->
          throwError $ InferError (FieldNotExisting name) (AreaReason area)
        _ -> do
          tv <- newTVar Star
          s3 <- unify (apply recordSubst fieldType) (recordType `fn` tv)

          let s          = compose s3 recordSubst
          let t          = apply s tv

          let recordExp' = updateType recordExp (apply s3 recordType)
          let solved = Slv.Solved t area (Slv.FieldAccess recordExp' fieldExp)

          return (s, [], t, solved)



-- INFER IF

inferIf :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferIf env exp@(Meta _ area (Src.If cond truthy falsy)) = do
  (s1, ps1, tcond  , econd  ) <- infer env cond
  (s2, ps2, ttruthy, etruthy) <- infer env truthy
  (s3, ps3, tfalsy , efalsy ) <- infer env falsy

  s4 <- catchError (unify tBool tcond)
                   (addConditionReason env exp cond area)
  s5 <- catchError (unify ttruthy tfalsy)
                   (addBranchReason env exp falsy area)

  let t = apply s5 ttruthy

  return
    ( s1 `compose` s2 `compose` s3 `compose` s4 `compose` s5
    , ps1 ++ ps2 ++ ps3
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

inferWhere :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferWhere env (Meta _ area (Src.Where exp iss)) = do
  (s, ps, t, e) <- infer env exp
  tv        <- newTVar Star
  pss       <- mapM (inferBranch env tv t) iss

  let ps' = concat $ T.mid <$> pss

  let issSubstitution = foldr1 compose $ (beg <$> pss) <> [s]

  s' <- unifyElems env (Slv.getType . lst <$> pss)

  let s'' = compose s' issSubstitution

  let
    iss =
      (\(Slv.Solved t a is) -> Slv.Solved (apply s'' t) a is) . lst <$> pss
  let wher = Slv.Solved (apply s'' tv) area
        $ Slv.Where (updateType e (apply s'' t)) iss
  return (s'', ps ++ ps', apply s'' tv, wher)


inferBranch
  :: Env -> Type -> Type -> Src.Is -> Infer (Substitution, [Pred], Slv.Is)
inferBranch env tv t (Meta _ area (Src.Is pat exp)) = do
  (ps, vars, t') <- inferPattern env pat
  s              <- catchError (unify t (removeSpread t')) (\(InferError e _) ->
      throwError $ InferError e
      (Reason (PatternTypeError exp pat) (envcurrentpath env) area))

  (s', ps', t'', e') <- infer (mergeVars env vars) exp
  s''           <- catchError (unify tv t'') (\(InferError e _) ->
      throwError $ InferError e
      (Reason (PatternTypeError exp pat) (envcurrentpath env) area))

  let t''' = extendRecord (s <> s'' <> s') t'
  s''' <- catchError (unify t t''') (\(InferError e _) ->
      throwError $ InferError e
      (Reason (PatternTypeError exp pat) (envcurrentpath env) area))

  let subst = s `compose` s' `compose` s'' `compose` s'''

  return
    ( subst
    , ps ++ ps'
    , Slv.Solved (apply subst (t''' `fn` t'')) area
      $ Slv.Is (updatePattern pat) (updateType e' (apply subst t''))
    )

removeSpread :: Type -> Type
removeSpread t = case t of
  TRecord fs o -> TRecord (M.filterWithKey (\k _ -> k /= "...") fs) o
  _            -> t

extendRecord :: Substitution -> Type -> Type
extendRecord s t = case t of
  TRecord fs _ ->
    let spread = M.lookup "..." fs
        fs'    = M.map (extendRecord s) fs
    in  case spread of
          Just (TVar tv) -> case M.lookup tv s of
            Just t' -> do
              case extendRecord s t' of
                TRecord fs'' _ -> TRecord
                  (M.filterWithKey (\k _ -> k /= "...") (fs' <> fs''))
                  True
                _ -> t
            _ -> t
          _ -> t

  _ -> t



-- INFER TYPEDEXP

inferTypedExp :: Env -> Src.Exp -> Infer (Substitution, [Pred], Type, Slv.Exp)
inferTypedExp env (Meta _ area (Src.TypedExp exp typing)) = do
  sc          <- typingToScheme env typing
  (ps :=> t) <- instantiate sc

  (s1, ps1, t1, e1) <- infer env exp
  s2           <- catchError (unify t t1) (\(InferError e _) ->
      throwError $ InferError e
      (Reason (TypeAndTypingMismatch exp typing t t1)
              (envcurrentpath env)
              area
      ))

  return
    ( s1 `compose` s2
    , ps
    , t
    , Slv.Solved
      t
      area
      (Slv.TypedExp (updateType e1 t) (updateTyping typing))
    )


makeGeneric :: M.Map String Int -> [Kind] -> Type -> (M.Map String Int, [Kind], Type)
makeGeneric gens ks t = case t of
  TVar (TV n k) -> case M.lookup n gens of
    Just x  -> (gens, ks, TGen x)
    Nothing -> (M.insert n (length gens) gens, ks <> [k], TGen (length gens))

  TCon _ -> (gens, ks, t)

  TApp l r ->
    let (gens', ks', l') = makeGeneric gens ks l
        (gens'', ks'', r') = makeGeneric gens' ks' r
    in  (gens'', ks'', TApp l' r')

  TRecord fs o ->
    let (gens', ks', fs') = M.foldrWithKey (\k t (gens'', ks'', fs'') ->
            let (gens''', ks''', t') = makeGeneric gens'' ks'' t
            in  (gens''', ks''', M.insert k t' fs'')
          ) (gens, ks, M.empty) fs
    in  (gens', ks', TRecord fs' o)


updatePlaceholders :: Substitution  -> Slv.Exp -> Slv.Exp
updatePlaceholders s (Slv.Solved t a e) = case e of
  Slv.Placeholder (ref, t) exp -> Slv.Solved t a $ Slv.Placeholder (ref, apply s t) (updatePlaceholders s exp)
  Slv.App abs arg final -> Slv.Solved t a $ Slv.App (updatePlaceholders s abs) (updatePlaceholders s arg) final
  Slv.Abs param es -> Slv.Solved t a $ Slv.Abs param (updatePlaceholders s <$> es)
  Slv.Where exp iss -> Slv.Solved t a $ Slv.Where (updatePlaceholders s exp) (updateIs s <$> iss)
  Slv.Assignment n exp -> Slv.Solved t a $ Slv.Assignment n (updatePlaceholders s exp)
  Slv.ListConstructor li -> Slv.Solved t a $ Slv.ListConstructor (updateListItem s <$> li)
  Slv.TypedExp exp typing -> Slv.Solved t a $ Slv.TypedExp (updatePlaceholders s exp) typing
  _ -> Slv.Solved t a e
 where
   updateIs :: Substitution -> Slv.Is -> Slv.Is
   updateIs s (Slv.Solved t a is) = case is of
     Slv.Is pat exp -> Slv.Solved t a $ Slv.Is pat (updatePlaceholders s exp)

   updateListItem :: Substitution -> Slv.ListItem -> Slv.ListItem
   updateListItem s li = case li of
     Slv.ListItem e -> Slv.ListItem $ updatePlaceholders s e
     Slv.ListSpread e -> Slv.ListSpread $ updatePlaceholders s e

isMethod :: Env -> Slv.Exp -> Bool
isMethod env (Slv.Solved _ _ e) = case e of
  Slv.Var n -> Just True == (M.lookup n (envmethods env) >> return True)
  _ -> False


getExpName :: Src.Exp -> Maybe String
getExpName (Meta _ _ exp) = case exp of
  Src.Assignment name _ ->
    return name

  Src.TypedExp (Meta _ _ (Src.Assignment name _)) _ ->
    return name

  Src.TypedExp (Meta _ _ (Src.Export (Meta _ _ (Src.Assignment name _)))) _ ->
    return name

  Src.Export (Meta _ _ (Src.Assignment name _)) ->
    return name

  _ -> Nothing


type Ambiguity       = (TVar, [Pred])

ambiguities         :: [TVar] -> [Pred] -> [Ambiguity]
ambiguities vs ps = [ (v, filter (elem v . ftv) ps) | v <- ftv ps \\ vs ]

split :: Env -> [TVar] -> [TVar] -> [Pred] -> Infer ([Pred], [Pred])
split env fs gs ps = do
  ps' <- reduce env ps
  let (ds, rs) = partition (all (`elem` fs) . ftv) ps'
  let as = ambiguities (fs ++ gs) rs
  if not (null as)
    then throwError $ InferError (AmbiguousType (head as)) NoReason
    else return (ds, rs)

verifyPred :: Type -> Pred -> Infer Bool
verifyPred t p@(IsIn n [t']) = case t of
  TApp l _ -> verifyPred l p
  TCon (TC "(->)" _) -> return True
  _ -> case t' of
      TCon _ -> return True
      TApp l _ -> verifyPred t (IsIn n [l])
      TVar x -> throwError $ InferError (AmbiguousType (x, [IsIn n [t']])) NoReason


inferImplicitlyTyped :: Env -> Src.Exp -> Infer (Substitution, [Pred], Env, Slv.Exp)
inferImplicitlyTyped env exp = do
  tv            <- newTVar Star

  let env' = case getExpName exp of
        Just n  -> extendVars env (n, toScheme tv)
        Nothing -> env

  (s, ps, t, e) <- infer env' exp
  s'            <- unify t tv
  let s'' = s `compose` s'
      ps' = apply s'' ps
      t'  = apply s'' tv
      fs  = ftv (apply s'' env)
      vs  = ftv t'
      gs  = vs \\ fs
  (ds, rs) <- split env' fs vs (trace ("QT: "<>ppShow (ps :=> t)<>"\nS'': "<>ppShow s''<>"\nFS: "<>ppShow fs<>"\nVS: "<>ppShow vs<>"\nPS': "<>ppShow ps') ps')

  mapM_ (verifyPred t') rs

  case getExpName exp of
    Just n  -> return (s'', ps', extendVars env' (n, quantify gs $ ps' :=> t'), e)
    Nothing -> return (s'', ps', env', e)


inferExplicitlyTyped :: Env -> Src.Exp -> Infer (Substitution, [Pred], Env, Slv.Exp)
inferExplicitlyTyped env e@(Meta _ a (Src.TypedExp exp typing)) = do
  sc            <- typingToScheme env typing

  let env' = case getExpName exp of
        Just n  -> extendVars env (n, sc)
        Nothing -> env

  (s, ps, t, e) <- infer env' exp
  (qs :=> t')  <- instantiate sc
  s' <- (`compose` s) <$> unify t' t

  let qs' = apply s' qs
      t'' = apply s' t'
      fs  = ftv (apply s' env)
      gs  = ftv t'' \\ fs
      sc' = quantify gs (qs' :=> t'')
  ps' <- filterM ((not <$>) . entail env' qs') (apply s' ps)
  (ds, rs) <- split env' fs gs ps'

  if sc /= sc' then
    throwError $ InferError (SignatureTooGeneral sc sc') (SimpleReason (envcurrentpath env') a)
  else  if not (null rs) then
    throwError $ InferError ContextTooWeak NoReason
  else do
    let e' = updateType e t''

    let qt = ps :=> t
    let qt' = apply s' qt
    let sc'' = quantify (ftv qt') qt'
    let env'' = case getExpName exp of
          Just n  -> extendVars env' (n, sc'')
          Nothing -> env'

    return (s', ps, env'', Slv.Solved t'' a (Slv.TypedExp e' (updateTyping typing)))


inferExps :: Env -> [Src.Exp] -> Infer [Slv.Exp]
inferExps _   []       = return []

inferExps env (e : xs) = do
  (s, ps, env', e') <- case e of
    Meta _ _ (Src.TypedExp _ _) -> inferExplicitlyTyped env e
    _                           -> inferImplicitlyTyped env e

  let e'' = insertClassPlaceholders e' (apply s ps)

  let e''' = updatePlaceholders s e''

  (e''' :) <$> inferExps env' xs


insertClassPlaceholders :: Slv.Exp -> [Pred] -> Slv.Exp
insertClassPlaceholders exp []     = exp
insertClassPlaceholders exp (p:ps) = case exp of
  Slv.Solved a t (Slv.Assignment n e) -> case predType p of
    TVar (TV n' _) -> 
      let exp' = Slv.Solved a t $ Slv.Assignment n (Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), predType p) e) 
      in  insertClassPlaceholders exp' ps
    _ -> exp

  Slv.Solved a t (Slv.TypedExp (Slv.Solved a' t' (Slv.Assignment n e)) _) -> case predType p of
    TVar (TV n' _) ->
      let exp' = Slv.Solved a t $ Slv.Assignment n (Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), predType p) e) 
      in  insertClassPlaceholders exp' ps
    _ -> exp

  -- Might need to move this into insertMethodClassPlaceholders
  Slv.Solved a t (Slv.Placeholder (ref, t') e) -> case predType p of
    TApp (TApp (TApp _ t1@(TCon (TC _ _))) t2@(TCon (TC _ _))) t3@(TCon (TC _ _)) ->
      let exp' = Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), t3) (Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), t2) (Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), t1) exp))
      in  insertClassPlaceholders exp' ps

    TApp (TApp _ t1@(TCon (TC _ _))) t2@(TCon (TC _ _)) ->
      let exp' = Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), t2) (Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), t1) exp)
      in  insertClassPlaceholders exp' ps

    TApp _ t'@(TCon (TC n' _)) ->
      let exp' = Slv.Solved a t $ Slv.Placeholder (Slv.ClassRef (predClass p), t') exp
      in  insertClassPlaceholders exp' ps

    _ -> exp

  Slv.Solved a t (Slv.App abs arg close) -> Slv.Solved a t (Slv.App (insertClassPlaceholders abs (p:ps)) (insertClassPlaceholders arg (p:ps)) close)

  _ -> exp



solveTable :: Src.Table -> Src.AST -> Infer Slv.Table
solveTable table ast = do
  (table, _) <- solveTable' table ast
  return table

solveTable' :: Src.Table -> Src.AST -> Infer (Slv.Table, Env)
solveTable' table ast@Src.AST { Src.aimports } = do
  -- First we resolve imports to update the env
  (inferredASTs, adts, vars, interfaces, methods) <- solveImports table aimports

  let importEnv = Env { envtypes       = adts
                      , envvars        = vars
                      , envcurrentpath = fromMaybe "" (Src.apath ast)
                      , envinterfaces  = interfaces
                      , envmethods     = methods
                      }

  -- Then we infer the ast
  env <- buildInitialEnv importEnv ast
  let envWithImports = env { envtypes = M.union (envtypes env) adts
                           , envvars  = M.union (envvars env) vars
                          --  , envmethods = envmethods env <> methods
                           }

  inferredAST <- inferAST envWithImports ast

  case Slv.apath inferredAST of
    Just fp -> return (M.insert fp inferredAST inferredASTs, envWithImports)



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


solveImports :: Src.Table -> [Src.Import] -> Infer (Slv.Table, TypeDecls, Vars, Interfaces, Methods)
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
  let adtExports = M.filterWithKey (\k _ -> k `elem` exportedADTNames) envADTs

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
            :=> TRecord (M.union exports (M.fromList (zip cvNames ts))) False
            )
          ]
        )

    (Just exports, _) -> return (exports, buildConstructorVars)

    (Nothing, _) ->
      throwError $ InferError (ImportNotFound modulePath) NoReason


  (nextTable, nextADTs, nextVars, nextInterfaces, nextMethods) <- solveImports table is

  mergedADTs                      <- do
    withNamespaces <- case imp of
      Meta _ _ (Src.DefaultImport namespace _ absPath) -> return
        $ M.mapKeys (mergeTypeDecl namespace absPath adtExports) adtExports

      _ -> return adtExports

    if M.intersection withNamespaces nextADTs == M.empty
      then return $ M.union withNamespaces nextADTs
      else throwError $ InferError FatalError NoReason

  let generify = \e ->
        let (gens, ks, t') = makeGeneric M.empty [] e
        in  Forall ks $ [] :=> t'


  let genericExports = M.map generify exports

  let allVars        = nextVars <> vars <> genericExports
  allVarsQt <- mapM instantiate allVars
  let allVarsT = M.map
        (\case
          (_ :=> t) -> t
        )
        allVarsQt

  return
    ( M.insert modulePath solvedAST (M.union solvedTable nextTable)
    , mergedADTs
    , M.map generify allVarsT
    , envinterfaces envSolved <> nextInterfaces
    , envmethods envSolved <> nextMethods
    )

solveImports _ [] = return (M.empty, envtypes initialEnv, envvars initialEnv, envinterfaces initialEnv, envmethods initialEnv)

isADT :: Slv.TypeDecl -> Bool
isADT Slv.ADT{} = True
isADT _         = False

mergeTypeDecl :: String -> FilePath -> M.Map String Type -> String -> String
mergeTypeDecl namespace absPath adts key = case M.lookup key adts of
  Just (TCon _) -> namespace <> "." <> key

  Just (TAlias path _ _ _) ->
    if path == absPath then namespace <> "." <> key else key
  _ -> key


updateInterface :: Src.Interface -> Slv.Interface
updateInterface (Src.Interface constraints name var methods) =
  Slv.Interface (updateTyping <$> constraints) name var (updateTyping <$> methods)

inferAST :: Env -> Src.AST -> Infer Slv.AST
inferAST env Src.AST { Src.aexps, Src.apath, Src.aimports, Src.atypedecls, Src.ainstances, Src.ainterfaces }
  = do
    inferredExps <- inferExps env aexps
    inferredInstances <- mapM (resolveInstance env) ainstances
    let updatedInterfaces = updateInterface <$> ainterfaces

    return Slv.AST { Slv.aexps       = inferredExps
                   , Slv.apath       = apath
                   , Slv.atypedecls  = updateADT <$> atypedecls
                   , Slv.aimports    = updateImport <$> aimports
                   , Slv.ainterfaces = updatedInterfaces
                   , Slv.ainstances  = inferredInstances
                   }


buildInstanceConstraint :: Src.Typing -> Pred
buildInstanceConstraint typing = case typing of
  (Meta _ _ (Src.TRComp n [Meta _ _ (Src.TRSingle var)])) ->
    IsIn n [TVar $ TV var Star]

resolveInstance :: Env -> Src.Instance -> Infer Slv.Instance
resolveInstance env (Src.Instance constraints interface ty dict) = do
  instanceType <- typingToType env ty
  let instancePred = IsIn interface [instanceType]
  let constraintPreds = buildInstanceConstraint <$> constraints
  dict' <- M.fromList <$> mapM (inferMethod env instancePred constraintPreds) (M.toList dict)
  return $ Slv.Instance (updateTyping <$> constraints) interface (updateTyping ty) dict'

inferMethod :: Env -> Pred -> [Pred] -> (Src.Name, Src.Exp) -> Infer (Slv.Name, Slv.Exp)
inferMethod env instancePred constraintPreds (mn, m) = do
  sc' <- lookupVar env mn
  qt@(mps :=> mt) <- instantiate sc'
  s1 <- unify mps [instancePred]
  let (mps' :=> mt') = apply s1 qt
  let qt'@(qs :=> t') = (mps' <> constraintPreds) :=> mt'

  let sc = quantify (ftv qt') qt'

  (s, ps, t, e) <- infer env m
  (qs :=> t')  <- instantiate sc
  s' <- (`compose` s) <$> unify t' t

  let qs' = apply s' qs
      t'' = apply s' t'
      fs  = ftv (apply s' env)
      gs  = ftv t'' \\ fs
      sc' = quantify gs (qs' :=> t'')
  ps' <- filterM ((not <$>) . entail env qs') (apply s' ps)
  (ds, rs) <- split env fs gs ps'

  if sc /= sc' then
    throwError $ InferError (SignatureTooGeneral sc sc') (SimpleReason (envcurrentpath env) emptyArea)
  else if not (null rs) then
    throwError $ InferError ContextTooWeak NoReason
  else do
    let e'  = updateType e t''
        (Slv.Solved _ _ (Slv.Assignment _ e'')) =
          insertClassPlaceholders (Slv.Solved t emptyArea $ Slv.Assignment mn e') (apply s' ps)
        e''' = updatePlaceholders s' e''
    return (mn, e''')

  -- e <- inferExps env [m]
  -- return (mn, head e)


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


-- -- TODO: Make it call inferAST so that inferAST can return an (Infer TBD)
-- -- Well, or just adapt it somehow
runInfer :: Env -> Src.AST -> Either InferError Slv.AST
runInfer env ast =
  fst <$> runExcept (runStateT (inferAST env ast) Unique { count = 0 })

