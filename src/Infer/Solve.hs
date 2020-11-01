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
import qualified AST
import qualified AST.Source as Src
import qualified AST.Solved as Slv
import           Infer.Infer
import           Infer.Type
import           Infer.Env
import           Infer.Substitute
import           Infer.Unify
import           Infer.Instantiate
import           Error.Error
import           Explain.Location
import           Explain.Reason
import Debug.Trace
import Text.Show.Pretty


infer :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
infer env lexp =

  let Located loc exp = lexp
  in  case exp of
    Src.LInt _            -> return (M.empty, num, applyLitSolve lexp num)
    Src.LStr _            -> return (M.empty, str, applyLitSolve lexp str)
    Src.LBool _           -> return (M.empty, bool, applyLitSolve lexp bool)

    Src.Var _             -> inferVar env lexp
    Src.Abs _ _           -> inferAbs env lexp
    Src.App _ _           -> inferApp env lexp
    Src.Assignment _ _    -> inferAssignment env lexp
    Src.Switch _ _        -> inferSwitch env lexp
    Src.Record _          -> inferRecord env lexp
    Src.FieldAccess _ _   -> inferFieldAccess env lexp
    Src.TypedExp _ _      -> inferTypedExp env lexp
    Src.ListConstructor _ -> inferListConstructor env lexp
    Src.JSExp c -> return (M.empty, TAny, Slv.Solved TAny (Located loc (Slv.JSExp c)))
    Src.Export _          -> inferExport env lexp
    Src.If _ _ _          -> inferIf env lexp


-- TODO: Should probably just take a Loc instead of the old Expression !
applyLitSolve :: Src.Exp -> Type -> Slv.Exp
applyLitSolve (Located loc exp) t = case exp of
  Src.LInt v  -> Slv.Solved t (Located loc $ Slv.LInt v)
  Src.LStr v  -> Slv.Solved t (Located loc $ Slv.LStr v)
  Src.LBool v -> Slv.Solved t (Located loc $ Slv.LBool v)

applyVarSolve :: Src.Exp -> Type -> Slv.Exp
applyVarSolve (Located loc (Src.Var v)) t = Slv.Solved t (Located loc $ Slv.Var v)

applyAbsSolve :: Src.Exp -> Slv.Name -> Slv.Exp -> Type -> Slv.Exp
applyAbsSolve (Located loc _) param body t = Slv.Solved t (Located loc $ Slv.Abs param body)

applyAppSolve :: Src.Exp -> Slv.Exp -> Slv.Exp -> Type -> Slv.Exp
applyAppSolve (Located loc _) abs arg t = Slv.Solved t (Located loc $ Slv.App abs arg)

applyAssignmentSolve :: Src.Exp -> Slv.Name -> Slv.Exp -> Type -> Slv.Exp
applyAssignmentSolve (Located loc _) n exp t = Slv.Solved t (Located loc $ Slv.Assignment n exp)


updateType :: Slv.Exp -> Type -> Slv.Exp
updateType (Slv.Solved t a) t' = Slv.Solved t' a


updatePattern :: Src.Pattern -> Slv.Pattern
updatePattern p = case p of
  Src.PVar name -> Slv.PVar name
  
  Src.PAny -> Slv.PAny

  Src.PCtor name patterns -> Slv.PCtor name (updatePattern <$> patterns)

  Src.PNum n -> Slv.PNum n
  Src.PStr n -> Slv.PStr n
  Src.PBool n -> Slv.PBool n
  
  Src.PCon n -> Slv.PCon n
  
  Src.PUserDef n -> Slv.PUserDef n
  
  Src.PRecord fields -> Slv.PRecord (updatePattern <$> fields)


updateTyping :: Src.Typing -> Slv.Typing
updateTyping t = case t of
  Src.TRSingle name -> Slv.TRSingle name

  Src.TRComp name vars -> Slv.TRComp name (updateTyping <$> vars)

  Src.TRArr l r -> Slv.TRArr (updateTyping l) (updateTyping r)

  Src.TRRecord fields -> Slv.TRRecord (updateTyping <$> fields)


-- INFER VAR

inferVar :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferVar env l@(Located loc (Src.Var n)) = case n of
  ('.' : name) -> do
    let s = Forall [TV "a"]
          $ TArr (TRecord (M.fromList [(name, TVar $ TV "a")])) (TVar $ TV "a")
    t <- instantiate s
    return (M.empty, t, applyVarSolve l t)

  _ -> (\(s, t) -> (s, t, applyVarSolve l t)) <$> lookupVar env n


-- INFER ABS

inferAbs :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferAbs env l@(Located loc (Src.Abs param body)) = do
  tv <- newTVar
  let env' = extendVars env (param, Forall [] tv)
  (s1, t1, e) <- infer env' body
  let t = apply s1 tv `TArr` t1
  return (s1, t, applyAbsSolve l param e t)--Slv.Solved t (Located loc $ Slv.Abs param e))


-- INFER APP

inferApp :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferApp env l@(Located loc (Src.App abs arg)) = do
  tv             <- newTVar
  (s1, t1, eabs) <- infer env abs
  (s2, t2, earg) <- infer env arg

  s3             <- case unify (apply s2 t1) (TArr t2 tv) of
    Right s -> return s
    Left e  -> throwError $ InferError e
      $ Reason (WrongTypeApplied arg) (getArea arg)
  let t = apply s3 tv

  return
    ( s3 `compose` s2 `compose` s1
    , t
    , applyAppSolve l eabs (updateType earg $ apply s3 t2) t
    )


-- INFER ASSIGNMENT

inferAssignment :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferAssignment env e@(Located loc (Src.Assignment name exp)) = case exp of
  (Located _ (Src.Abs _ _)) -> do
    (s1, t1, e1) <- infer env exp

    case M.lookup name $ envtypings env of
      Just (Forall fv t2) -> do
        let bv = S.toList $ ftv t2
        it2 <- instantiate (Forall (fv <> bv) t2)
        s2  <- unifyToInfer env $ unify (trace ("T1: "<>ppShow t1) t1) (trace ("IT2: "<>ppShow it2) it2)
        return
          ( s2 `compose` s1
          , it2
          , applyAssignmentSolve e name (updateType e1 it2) it2
          )

      Nothing -> return (s1, t1, applyAssignmentSolve e name e1 t1)

  _ -> do
    (s1, t1, e1) <- infer env exp
    return (s1, t1, applyAssignmentSolve e name e1 t1)


-- INFER EXPORT

inferExport :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferExport env (Located loc (Src.Export exp)) = do
  (s, t, e) <- infer env exp
  return (s, t, Slv.Solved t (Located loc (Slv.Export e)))


-- INFER RECORD

inferRecord :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferRecord env (Located loc (Src.Record fields)) = do
  inferred <- mapM (infer env) fields
  let inferredFields = M.map trd inferred
      recordType     = TRecord $ M.map mid inferred
  return
    ( M.empty
    , recordType
    , Slv.Solved recordType (Located loc (Slv.Record inferredFields))
    )


-- INFER TYPEDEXP

-- TODO: Needs to handle quantified variables ?
-- TODO: Add TComp
-- TODO: Add TArr
-- So that we can write a type :
-- :: (a -> b) -> List a -> List b
inferTypedExp :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferTypedExp _ (Located loc (Src.TypedExp exp typing)) = do
  t <- typingToType typing
  
  -- TODO: Handle other cases
  let e = case exp of
        Located loc (Src.Var name) -> Slv.Solved t (Located loc (Slv.Var name))

  return (M.empty, t, Slv.Solved t (Located loc (Slv.TypedExp e (updateTyping typing))))

typingToType :: Src.Typing -> Infer Type
typingToType (Src.TRSingle t) | t == "Num"    = return $ TCon CNum
                           | t == "Bool"   = return $ TCon CBool
                           | t == "String" = return $ TCon CString
                           | t == "Void"   = return $ TCon CVoid
                           | otherwise     = return $ TVar $ TV t

typingToType (Src.TRComp t ts) = do
  params <- mapM typingToType ts
  return $ TComp t params

typingToType (Src.TRArr l r) = do
  l' <- typingToType l
  r' <- typingToType r
  return $ TArr l' r'

typingToType (Src.TRRecord f) = do
  f' <- mapM typingToType f
  return $ TRecord f'


-- INFER LISTCONSTRUCTOR

inferListConstructor :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferListConstructor env (Located loc (Src.ListConstructor elems)) = case elems of
  [] -> let t = TComp "List" [TVar $ TV "a"]
        in  return (M.empty, t, Slv.Solved t (Located loc (Slv.ListConstructor [])))

  elems -> do
    inferred <- mapM (infer env) elems
    let (_, t1, _) = head inferred
    let t          = TComp "List" [t1]
    s <- unifyToInfer env $ unifyElems t1 (mid <$> inferred)
    return (s, t, Slv.Solved t (Located loc (Slv.ListConstructor (trd <$> inferred))))


-- INFER FIELD ACCESS

inferFieldAccess :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferFieldAccess env (Located loc (Src.FieldAccess rec@(Located l arg) abs@(Located _ (Src.Var ('.':name))))) = do
  (rs, rt, re) <- infer env (Located l arg)

  let ft = case rt of
        TRecord fields -> M.lookup name fields
        _              -> Nothing

  case ft of
    Just t -> do
      (s1, _, e1) <- infer env abs
      return (rs `compose` s1, t, Slv.Solved t (Located loc (Slv.FieldAccess re e1)))

    Nothing -> do
      (s1, t1, e1) <- inferApp env (Located loc (Src.App abs rec))
      let rt' = apply s1 rt
      return (rs `compose` s1, t1, Slv.Solved t1 (Located loc (Slv.FieldAccess (updateType re rt') e1)))


-- INFER IF

inferIf :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferIf env (Located loc (Src.If cond truthy falsy)) = do
  (_, tcond, econd)     <- infer env cond
  (_, ttruthy, etruthy) <- infer env truthy
  (_, tfalsy, efalsy)   <- infer env falsy

  s1 <- unifyToInfer env $ unify tcond (TCon CBool)
  s2 <- unifyToInfer env $ unify ttruthy tfalsy

  return (s1 `compose` s2, ttruthy, Slv.Solved ttruthy (Located loc (Slv.If econd etruthy efalsy)))


-- INFER SWITCH

inferSwitch :: Env -> Src.Exp -> Infer (Substitution, Type, Slv.Exp)
inferSwitch env (Located loc (Src.Switch exp cases)) = do
  (se, te, ee)  <- infer env exp

  inferredCases <- mapM (inferCase env te) cases
  let casesSubstitution = foldr1 compose $ se : (beg <$> inferredCases)
  let casesTypes        = mid <$> inferredCases
  let cases             = trd <$> inferredCases

  let typeMatrix        = (, casesTypes) <$> casesTypes
  s <-
    foldr1 compose
      <$> mapM (\(t, ts) -> unifyToInfer env $ unifyPatternElems (apply casesSubstitution t) ts)
               typeMatrix

  let updatedCases =
        (\(t, e) -> e { Slv.casetype = Just $ apply s t }) <$> zip casesTypes cases

  let (TArr _ switchType) = (apply s . head) casesTypes

  return
    ( s
    , switchType
    , Slv.Solved switchType (Located loc $ Slv.Switch (updateType ee (apply s te)) updatedCases)
    )

 where

  inferCase :: Env -> Type -> Src.Case -> Infer (Substitution, Type, Slv.Case)
  inferCase e tinput c@Src.Case { Src.casepattern, Src.caseexp, Src.casepos } = do
    tp           <- buildPatternType e casepattern
    e'           <- generateCaseEnv tp e casepattern

    (se, te, ee) <- infer e' caseexp
    let tarr  = TArr (apply se tp) te
    let tarr' = TArr (apply se tinput) te
    su <- unifyToInfer env $ unifyPatternElems tarr [tarr']

    let sf = su `compose` se

    return
      ( sf
      , tarr
      , Slv.Case { Slv.casetype = Just $ apply sf tarr
                 , Slv.caseexp  = updateType ee $ apply sf te
                 , Slv.casepos = casepos
                 , Slv.casepattern = updatePattern casepattern
                 }
      )

  buildPatternType :: Env -> Src.Pattern -> Infer Type
  buildPatternType e@Env { envvars } pat = case pat of
    Src.PVar  v        -> return $ TVar $ TV v

    Src.PCon  "String" -> return $ TCon CString
    Src.PCon  "Bool"   -> return $ TCon CBool
    Src.PCon  "Num"    -> return $ TCon CNum

    Src.PStr  _        -> return $ TCon CString
    Src.PBool _        -> return $ TCon CBool
    Src.PNum  _        -> return $ TCon CNum

    Src.PAny           -> return $ TVar $ TV "a"

    Src.PRecord fields -> TRecord . M.fromList <$> mapM
      (\(k, v) -> (k, ) <$> buildPatternType e v)
      (M.toList fields)

    Src.PCtor n as -> do
      (Forall fv ctor) <- case M.lookup n envvars of
        Just x  -> return x
        Nothing -> throwError $ InferError (UnknownType n) NoReason

      let rt = arrowReturnType ctor
      ctor'  <- argPatternsToArrowType rt as
      ctor'' <- instantiate $ Forall fv ctor
      s      <- unifyToInfer env $ unify ctor' ctor''
      return $ apply s rt

     where
      argPatternsToArrowType :: Type -> [Src.Pattern] -> Infer Type
      argPatternsToArrowType rt (f : xs) = do
        l <- buildPatternType e f
        r <- argPatternsToArrowType rt xs
        return $ TArr l r
      argPatternsToArrowType _  [x] = buildPatternType e x
      argPatternsToArrowType rt []  = return rt

    _ -> return $ TVar $ TV "x"


  generateCaseEnv :: Type -> Env -> Src.Pattern -> Infer Env
  generateCaseEnv t e@Env { envvars } pat = case (pat, t) of
    (Src.PVar v, t') -> do
      return $ extendVars e (v, Forall [] t')

    (Src.PRecord fields, TRecord fields') ->
      let allFields = zip (M.elems fields) (M.elems fields')
      in  foldrM (\(p, t) e' -> generateCaseEnv t e' p) e allFields

    (Src.PCtor cname as, t) -> do
      ctor <- findConstructor cname

      case (ctor, as) of
        (TArr a _, [a']) -> do
          generateCaseEnv a e a'

        (TArr a (TArr b _), [a', b']) -> do
          e1 <- generateCaseEnv a e a'
          generateCaseEnv b e1 b'

        (TArr a (TArr b (TArr c _)), [a', b', c']) -> do
          e1 <- generateCaseEnv a e a'
          e2 <- generateCaseEnv b e1 b'
          generateCaseEnv c e2 c'

        _ -> return e

    _ -> return e

   where
    findConstructor :: String -> Infer Type
    findConstructor cname = case M.lookup cname envvars of
      Just (Forall _ t) -> return t

      Nothing           -> throwError $ InferError (UnknownType cname) NoReason



inferExps :: Env -> [Src.Exp] -> Infer [Slv.Exp]
inferExps _   []       = return []

inferExps env [exp   ] = (:[]) . trd <$> infer env exp

inferExps env (e : xs) = do
  (_, t, e') <- infer env e
  let exp = Slv.extractExp e'
  let env' = case exp of
        -- TODO: We need to add a case where that name is already in the env.
        -- Reassigning a name should not be allowed.
        Slv.Assignment name _ -> extendVars env (name, Forall ((S.toList . ftv) t) t)

        Slv.TypedExp (Slv.Solved _ (Located _ (Slv.Var name))) _ ->
          extendTypings env (name, Forall ((S.toList . ftv) t) t)

        _ -> env

  (e':) <$> inferExps env' xs


trd :: (a, b, c) -> c
trd (_, _, x) = x

mid :: (a, b, c) -> b
mid (_, b, _) = b

beg :: (a, b, c) -> a
beg (a, _, _) = a


inferAST :: FilePath -> Src.Table -> Src.AST -> Infer Slv.Table
inferAST rootPath table ast@Src.AST { Src.aimports } = do
  env <- buildInitialEnv ast

  (inferredASTs, imports) <- resolveImports rootPath table aimports
  let envWithImports = env { envimports = imports }

  inferredAST <- inferASTExps envWithImports ast

  case Slv.apath inferredAST of

    Just fp -> return $ M.insert fp inferredAST inferredASTs

    Nothing -> throwError $ InferError ASTHasNoPath NoReason



exportedExps :: Slv.AST -> Infer [(Slv.Name, Slv.Exp)]
exportedExps Slv.AST { Slv.aexps, Slv.apath } = case apath of
  Just p  -> mapM (bundleExports p) $ filter isExport aexps

  Nothing -> throwError $ InferError ASTHasNoPath NoReason
  
  where
    bundleExports _ (Slv.Solved _ (Located _ (Slv.Export e))) =
      let (Slv.Solved _ (Located _ (Slv.Assignment n e'))) = e
      in  return (n, e')
    
    isExport :: Slv.Exp -> Bool
    isExport a = case a of
      (Slv.Solved _ (Located _ (Slv.Export _))) -> True

      _                                     -> False


-- -- TODO: Needs to handle data types as well.
resolveImports :: FilePath -> Src.Table -> [Src.Import] -> Infer (Slv.Table, Imports)
resolveImports root table (imp:is) = do
  let modulePath = case imp of
        Src.NamedImport _ n   -> n

        Src.DefaultImport _ n -> n

  let path = root <> modulePath <> ".mad"
  
  solvedAST <- case AST.findAST table path of

        Right ast -> do
          env <- buildInitialEnv ast
          inferASTExps env ast

        Left (AST.ASTNotFound path) -> throwError $ InferError (ImportNotFound path "") NoReason

        Left (AST.ImportNotFound path _) -> throwError $ InferError (ImportNotFound path "") NoReason

  exportedExps <- M.fromList <$> exportedExps solvedAST
  let exportedTypes = mapM (return . Slv.getType) exportedExps

  exports <- case (exportedTypes, imp) of
    (Just exports, Src.DefaultImport alias _) -> return $ M.fromList [(alias, TRecord exports)]

    (Just exports, _)                         -> return exports

    (Nothing, _)                              -> throwError $ InferError (ImportNotFound path "") NoReason

  (nextTable, nextExports) <- resolveImports root table is

  return (M.insert path solvedAST nextTable, M.union exports nextExports)

resolveImports _ _ [] = return (M.empty, M.empty)


inferASTExps :: Env -> Src.AST -> Infer Slv.AST
inferASTExps env Src.AST { Src.aexps, Src.apath, Src.aimports, Src.aadts } = do
  inferredExps <- inferExps env aexps
  return Slv.AST { Slv.aexps = inferredExps
                 , Slv.apath = apath
                 , Slv.aadts = updateADT <$> aadts
                 , Slv.aimports = updateImport <$> aimports
                 }

updateImport :: Src.Import -> Slv.Import
updateImport i = case i of
  Src.NamedImport ns fp  -> Slv.NamedImport ns fp

  Src.DefaultImport n fp -> Slv.DefaultImport n fp


updateADT :: Src.ADT -> Slv.ADT
updateADT Src.ADT { Src.adtname, Src.adtparams, Src.adtconstructors } =
  Slv.ADT { Slv.adtname = adtname
          , Slv.adtparams = adtparams
          , Slv.adtconstructors = updateADTConstructor <$> adtconstructors}

updateADTConstructor :: Src.ADTConstructor -> Slv.ADTConstructor
updateADTConstructor Src.ADTConstructor { Src.adtcname, Src.adtcargs }
  = Slv.ADTConstructor { Slv.adtcname = adtcname
                       , Slv.adtcargs = (updateTyping <$>) <$> adtcargs
                       }


unifyToInfer :: Env -> Either TypeError Substitution -> Infer Substitution
unifyToInfer env u = case u of
  Right s -> return s
  Left  e -> throwError $ InferError e NoReason


-- -- TODO: Make it call inferAST so that inferAST can return an (Infer TBD)
-- -- Well, or just adapt it somehow
runInfer :: Env -> Src.AST -> Either InferError Slv.AST
runInfer env ast
  = fst <$> runExcept (runStateT (inferASTExps env ast) Unique { count = 0 })
