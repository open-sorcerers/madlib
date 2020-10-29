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
import           Grammar
import           Data.Foldable                  ( foldrM )
import qualified AST
import           Infer.Type
import           Infer.Env
import           Infer.Substitute
import           Infer.Unify
import           Infer.Instantiate


-- TODO: Move Env to a ReaderMonad
infer :: Env -> Exp -> Infer (Substitution, Type, Exp)
infer env exp =
  -- Push backtrace here
  case exp of
    l@LInt{} -> return (M.empty, TCon CNum, l { etype = Just $ TCon CNum })
    l@LStr{} -> return (M.empty, TCon CString, l { etype = Just $ TCon CString })
    l@LBool{} -> return (M.empty, TCon CBool, l { etype = Just $ TCon CBool })

    v@Var {}          -> inferVar env v
    abs@Abs {}        -> inferAbs env abs
    app@App { eabs = Var { ename = '.':_ } } -> inferFieldAccess env app
    app@App {}        -> inferApp env app
    ass@Assignment {} -> inferAssignment env ass
    sw@Switch {}      -> inferSwitch env sw
    te@TypedExp {} -> inferTypedExp env te
    rec@Record {} -> inferRecord env rec
    lc@ListConstructor {} -> inferListConstructor env lc
    e@JSExp { etype = Just t } -> return (M.empty, t, e)


-- INFER RECORD

inferRecord :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferRecord env rec@Record { erfields } = do
  inferred <- mapM (infer env) erfields
  let inferredFields = M.map trd inferred
      recordType     = TRecord $ M.map mid inferred
  return
    ( M.empty
    , recordType
    , rec { etype = Just recordType, erfields = inferredFields }
    )


-- INFER TYPEDEXP

-- TODO: Needs to handle quantified variables ?
-- TODO: Add TComp
-- TODO: Add TArr
-- So that we can write a type :
-- :: (a -> b) -> List a -> List b
inferTypedExp :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferTypedExp _ te@TypedExp { etyping } = do
  t <- typingsToType etyping
  return (M.empty, t, te { etype = Just t })


-- INFER LISTCONSTRUCTOR

inferListConstructor :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferListConstructor env lc@ListConstructor { eelems } = case eelems of
  [] -> let t = TComp "List" [TVar $ TV "a"]
        in  return (M.empty, t, lc { etype = Just t })

  elems -> do
    inferred <- mapM (infer env) elems
    let (s1, t1, e1) = head inferred
    let t            = TComp "List" [t1]
    s <- unifyElems t1 (mid <$> inferred)

    return (s, t, lc { etype = Just t })


-- INFER VAR

inferVar :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferVar env v@Var { ename } = case ename of
  ('.' : name) -> do
    let s = Forall [TV "a"]
          $ TArr (TRecord (M.fromList [(name, TVar $ TV "a")])) (TVar $ TV "a")
    t <- instantiate s
    return (M.empty, t, v { etype = Just t })

  _ -> (\(s, t) -> (s, t, v { etype = Just t })) <$> lookupVar env ename


-- INFER ABS

inferAbs :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferAbs env abs@Abs { eparam, ebody } = do
  tv <- newTVar
  let env' = extendVars env (eparam, Forall [] tv)
  (s1, t1, e) <- infer env' ebody
  let t = apply s1 tv `TArr` t1
  return (s1, t, abs { ebody = e, etype = Just t })


-- INFER APP

inferApp :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferApp env app@App { eabs, earg } = do
  tv           <- newTVar
  (s1, t1, e1) <- infer env eabs
  (s2, t2, e2) <- infer env earg

  s3           <- unify (apply s2 t1) (TArr t2 tv)
  let t = apply s3 tv

  return
    ( s3 `compose` s2 `compose` s1
    , t
    , app { eabs  = e1
          , earg  = e2 { etype = Just $ apply s3 t2 }
          , etype = Just t
          }
    )


-- INFER FIELD ACCESS

inferFieldAccess :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferFieldAccess env app@App { eabs = abs@Var { ename = '.':name }, earg } = do
  (_, rt, _) <- case etype earg of
        Just x -> return (M.empty, x, earg)
        Nothing -> infer env earg

  let ft = case rt of
        TRecord fields -> M.lookup name fields
        _ -> Nothing -- That one should be a fail then

  case ft of

    Just t -> do
      (_, t1, _) <- infer env abs
      return (M.empty, t, app { etype = Just t, earg = earg { etype = Just rt }, eabs = abs { etype = Just t1 } })

    Nothing -> inferApp env app


-- INFER ASSIGNMENT

inferAssignment :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferAssignment env ass@Assignment { eexp, ename } = case eexp of
  Abs{} -> do
    (s1, t1, e1) <- infer env eexp

    case M.lookup ename $ envtypings env of
      Just (Forall fv t2) -> do
        let bv = S.toList $ ftv t2
        it2 <- instantiate (Forall (fv <> bv) t2)
        s2  <- unify t1 it2
        return
          ( s2 `compose` s1
          , it2
          , ass { eexp = e1 { etype = Just it2 }, etype = Just it2 }
          )

      Nothing -> return (s1, t1, ass { eexp = e1, etype = Just t1 })

  _ -> do
    (s1, t1, e1) <- infer env eexp
    return (s1, t1, ass { eexp = e1, etype = Just t1 })


-- INFER SWITCH

inferSwitch :: Env -> Exp -> Infer (Substitution, Type, Exp)
inferSwitch env sw@Switch { ecases, eexp } = do
  (se, te, ee)  <- infer env eexp

  inferredCases <- mapM (inferCase env te) ecases
  let casesSubstitution = foldr1 compose $ se : (beg <$> inferredCases)
  let casesTypes        = mid <$> inferredCases
  let cases             = trd <$> inferredCases

  let typeMatrix        = (, casesTypes) <$> casesTypes
  s <-
    foldr1 compose
      <$> mapM (\(t, ts) -> unifyPatternElems (apply casesSubstitution t) ts)
               typeMatrix

  let updatedCases =
        (\(t, e) -> e { casetype = Just $ apply s t }) <$> zip casesTypes cases

  let (TArr _ switchType) = (apply s . head) casesTypes

  return
    ( s
    , switchType
    , sw { ecases = updatedCases
         , etype  = Just switchType
         , eexp   = ee { etype = Just $ apply s te }
         }
    )

 where

  inferCase :: Env -> Type -> Case -> Infer (Substitution, Type, Case)
  inferCase e tinput c@Case { casepattern, caseexp } = do
    tp           <- buildPatternType e casepattern
    e'           <- generateCaseEnv tp e casepattern

    (se, te, ee) <- infer e' caseexp
    let tarr  = TArr (apply se tp) te
    let tarr' = TArr (apply se tinput) te
    su <- unifyPatternElems tarr [tarr']

    let sf = su `compose` se

    return
      ( sf
      , tarr
      , c { casetype = Just $ apply sf tarr
          , caseexp  = ee { etype = Just $ apply sf te }
          }
      )

  buildPatternType :: Env -> Pattern -> Infer Type
  buildPatternType e@Env { envvars } pat = case pat of
    PVar  v        -> return $ TVar $ TV v

    PCon  "String" -> return $ TCon CString
    PCon  "Bool"   -> return $ TCon CBool
    PCon  "Num"    -> return $ TCon CNum

    PStr  _        -> return $ TCon CString
    PBool _        -> return $ TCon CBool
    PNum  _        -> return $ TCon CNum

    PAny           -> return $ TVar $ TV "a"

    PRecord fields -> TRecord . M.fromList <$> mapM
      (\(k, v) -> (k, ) <$> buildPatternType e v)
      (M.toList fields)

    PCtor n as -> do
      (Forall fv ctor) <- case M.lookup n envvars of
        Just x  -> return x
        Nothing -> throwError $ UnknownType n

      let rt = arrowReturnType ctor
      ctor'  <- argPatternsToArrowType rt as
      ctor'' <- instantiate $ Forall fv ctor
      s      <- unify ctor' ctor''
      return $ apply s rt

     where
      argPatternsToArrowType :: Type -> [Pattern] -> Infer Type
      argPatternsToArrowType rt (f : xs) = do
        l <- buildPatternType e f
        r <- argPatternsToArrowType rt xs
        return $ TArr l r
      argPatternsToArrowType _  [x] = buildPatternType e x
      argPatternsToArrowType rt []  = return rt

    _ -> return $ TVar $ TV "x"


  generateCaseEnv :: Type -> Env -> Pattern -> Infer Env
  generateCaseEnv t e@Env { envvars } pat = case (pat, t) of
    (PVar v, t') -> do
      return $ extendVars e (v, Forall [] t')

    (PRecord fields, TRecord fields') ->
      let allFields = zip (M.elems fields) (M.elems fields')
      in  foldrM (\(p, t) e' -> generateCaseEnv t e' p) e allFields

    (PCtor cname as, t) -> do
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

      Nothing           -> throwError $ UnknownType cname


-- TODO: If we want to allow multiple Exp per abstraction, we'll have to move this and
-- make it work at any depth of the AST.
inferExps :: Env -> [Exp] -> Infer [Exp]
inferExps _   []       = return []

inferExps env [exp   ] = (:[]) . trd <$> infer env exp

inferExps env (e : xs) = do
  (_, t, e') <- infer env e
  let env' = case e of
        -- TODO: We need to add a case where that name is already in the env.
        -- Reassigning a name should not be allowed.
        Assignment { ename } -> extendVars env (ename, Forall ((S.toList . ftv) t) t)

        TypedExp { eexp = Var { ename } } ->
          extendTypings env (ename, Forall ((S.toList . ftv) t) t)

        _ -> env

  (e':) <$> inferExps env' xs


trd :: (a, b, c) -> c
trd (_, _, x) = x

mid :: (a, b, c) -> b
mid (_, b, _) = b

beg :: (a, b, c) -> a
beg (a, _, _) = a


-- TODO: Make it call inferAST so that inferAST can return an (Infer TBD)
-- Well, or just adapt it somehow
runInfer :: Env -> AST -> Either InferError AST
runInfer env ast = (\e -> ast { aexps = e }) <$> inferredExps
 where
  inferredExps = fst
    <$> runExcept (runStateT (inferExps env $ aexps ast) Unique { count = 0 })


inferAST :: FilePath -> AST.ASTTable -> AST -> Infer AST.ASTTable
inferAST rootPath table ast@AST { aimports } = do
  env <- buildInitialEnv ast

  (inferredASTs, imports) <- resolveImports rootPath table aimports
  let envWithImports = env { envimports = imports }

  inferredAST <- inferASTExps envWithImports ast

  case apath inferredAST of

    Just fp -> return $ M.insert fp inferredAST inferredASTs

    Nothing -> throwError ASTHasNoPath



exportedExps :: AST -> Infer [(Name, Exp)]
exportedExps AST { aexps, apath } = case apath of
  Just p  -> mapM (bundleExports p) $ filter isExport aexps

  Nothing -> throwError ASTHasNoPath
  
  where 
    bundleExports _ exp@Assignment { ename } = return (ename, exp)
    
    isExport :: Exp -> Bool
    isExport a = case a of

      Assignment { eexported } -> eexported

      _                        -> False


-- TODO: Needs to handle data types as well.
resolveImports :: FilePath -> AST.ASTTable -> [Import] -> Infer (AST.ASTTable, Imports)
resolveImports root table (imp:is) = do
  let modulePath = ipath imp
  let path = root <> modulePath <> ".mad"
  
  inferredAST <- case AST.findAST table path of

        Right ast -> do
          env <- buildInitialEnv ast
          inferASTExps env ast

        Left (AST.ASTNotFound path) -> throwError $ ImportNotFound path ""

        Left (AST.ImportNotFound path _) -> throwError $ ImportNotFound path ""

  exportedExps <- M.fromList <$> exportedExps inferredAST
  let exportedTypes = mapM etype exportedExps

  exports <- case (exportedTypes, imp) of
    (Just exports, DefaultImport { ialias }) -> return $ M.fromList [(ialias, TRecord exports)]

    (Just exports, _)                        -> return exports

    (Nothing, _)                             -> throwError $ ImportNotFound path ""

  (nextTable, nextExports) <- resolveImports root table is

  return (M.union (M.insert path inferredAST table) nextTable, M.union exports nextExports)

resolveImports _ _ [] = return (M.empty, M.empty)


inferASTExps :: Env -> AST -> Infer AST
inferASTExps env ast@AST { aexps } = do
  inferredExps <- inferExps env aexps
  return ast { aexps = inferredExps }


typingsToType :: TypeRef -> Infer Type
typingsToType (TRSingle t) | t == "Num"    = return $ TCon CNum
                           | t == "Bool"   = return $ TCon CBool
                           | t == "String" = return $ TCon CString
                           | t == "Void"   = return $ TCon CVoid
                           | otherwise     = return $ TVar $ TV t

typingsToType (TRComp t ts) = do
  params <- mapM typingsToType ts
  return $ TComp t params

typingsToType (TRArr l r) = do
  l' <- typingsToType l
  r' <- typingsToType r
  return $ TArr l' r'

typingsToType (TRRecord f) = do
  f' <- mapM typingsToType f
  return $ TRecord f'

