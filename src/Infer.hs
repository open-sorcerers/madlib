{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
module Infer where

import qualified Data.Map                      as M
import qualified Data.Set                      as S
import           Control.Monad.Except
import           Control.Monad.State
import           Grammar
import           Debug.Trace
import           Data.Foldable                  ( Foldable(foldl') )
import           Data.Char                      ( isLower )


newtype TVar = TV String
  deriving (Show, Eq, Ord)

data Type
  = TVar TVar         -- Variable type
  | TCon TCon         -- Constant type
  | TArr Type Type    -- Arrow type
  -- TODO: Maybe move back to TComp TCon [TVar] and construct the Type from TVar
  -- in needed places
  -- TODO: Rename TADT ?
  | TComp TCon [Type] -- Composite type
  deriving (Show, Eq, Ord)

data TCon
  = CString
  | CNum
  | CBool
  | CUserDef String
  deriving (Show, Eq, Ord)

infixr `TArr`

data Scheme = Forall [TVar] Type
  deriving (Show, Eq, Ord)

-- TODO: Convert back to a simple type
type Vars = M.Map String Scheme
type ADTs = M.Map String Type

data Env
  = Env
    { envvars :: Vars
    , envadts :: ADTs
    }
    deriving(Eq, Show)

type Substitution = M.Map TVar Type

data InferError
  = InfiniteType TVar Type
  | UnboundVariable String
  | UnificationError Type Type
  deriving (Show, Eq, Ord)

newtype Unique = Unique { count :: Int }
  deriving (Show, Eq, Ord)

type Infer a = forall m . (MonadError InferError m, MonadState Unique m) => m a


class Substitutable a where
  apply :: Substitution -> a -> a
  ftv   :: a -> S.Set TVar

instance Substitutable Type where
  apply _ (  TCon a           ) = TCon a
  apply s t@(TVar a           ) = M.findWithDefault t a s
  apply s (  t1    `TArr` t2  ) = apply s t1 `TArr` apply s t2
  apply s (  TComp main   vars) = TComp main (apply s <$> vars)

  ftv TCon{}              = S.empty
  ftv (TVar a           ) = S.singleton a
  ftv (t1    `TArr` t2  ) = ftv t1 `S.union` ftv t2
  ftv (TComp _      vars) = foldl' (\s v -> S.union s $ ftv v) S.empty vars

instance Substitutable Scheme where
  apply s (Forall as t) = Forall as $ apply s' t
    where s' = foldr M.delete s as
  ftv (Forall as t) = S.difference (ftv t) (S.fromList as)

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = foldr (S.union . ftv) S.empty

instance Substitutable Env where
  apply s env = env { envvars = M.map (apply s) $ envvars env }
  ftv env = ftv $ M.elems $ envvars env


extendVars :: Env -> (String, Scheme) -> Env
extendVars env (x, s) = env { envvars = M.insert x s $ envvars env }


lookupVar :: Env -> String -> Infer (Substitution, Type)
lookupVar env x = do
  case M.lookup x $ envvars env of
    Nothing -> throwError $ UnboundVariable x
    Just s  -> do
      t <- instantiate s
      return (M.empty, t)


letters :: [String]
letters = [1 ..] >>= flip replicateM ['a' .. 'z']

newTVar :: Infer Type
newTVar = do
  s <- get
  put s { count = count s + 1 }
  return $ TVar $ TV (letters !! count s)


instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const newTVar) as
  let s = M.fromList $ zip as as'
  return $ apply s t


compose :: Substitution -> Substitution -> Substitution
s1 `compose` s2 = M.map (apply s1) $ M.union s2 s1


occursCheck :: Substitutable a => TVar -> a -> Bool
occursCheck a t = S.member a $ ftv t


bind :: TVar -> Type -> Infer Substitution
bind a t | t == TVar a     = return M.empty
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return $ M.singleton a t


unify :: Type -> Type -> Infer Substitution
unify (l `TArr` r) (l' `TArr` r') = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return (s2 `compose` s1)

unify (TComp main vars) (TComp main' vars') = do
  s1 <- unify (TCon main) (TCon main')
  let z = zip vars vars'
  s2 <- unifyVars s1 z
  return (s2 `compose` s1)
 where
  unifyVars :: Substitution -> [(Type, Type)] -> Infer Substitution
  unifyVars s ((tp, tp') : xs) = do
    s1 <- unify (apply s tp) (apply s tp')
    unifyVars s1 xs
  unifyVars s [(tp, tp')] = unify (apply s tp) (apply s tp')
  unifyVars s _           = return s

unify (TVar a) t                 = bind a t
unify t        (TVar a)          = bind a t
unify (TCon a) (TCon b) | a == b = return M.empty
unify t1 t2                      = throwError $ UnificationError t1 t2


infer :: Env -> Exp -> Infer (Substitution, Type)
infer env Var { ename }         = lookupVar env ename

infer env Abs { eparam, ebody } = do
  tv <- newTVar
  let env' = extendVars env (eparam, Forall [] tv)
  (s1, t1) <- infer env' ebody
  return (s1, apply s1 tv `TArr` t1)

infer env App { eabs, earg } = do
  tv       <- newTVar
  (s1, t1) <- infer env eabs
  (s2, t2) <- infer (apply s1 env) earg
  s3       <- unify (apply s2 t1) (TArr t2 tv)
  return (s3 `compose` s2 `compose` s1, apply s3 tv)

infer env Assignment { eexp, ename } = case eexp of
  Abs{} -> do
    (s1, t1) <- infer env eexp
    s2       <- case M.lookup ename $ envvars env of
      Just t2 -> instantiate t2 >>= unify t1
      Nothing -> return s1
    return (s2 `compose` s1, t1)
  _ -> infer env eexp

infer _ LInt{}               = return (M.empty, TCon CNum)
infer _ LStr{}               = return (M.empty, TCon CString)
infer _ LBool{}              = return (M.empty, TCon CBool)

infer _ TypedExp { etyping } = return (M.empty, typingsToType etyping)

infer _ _                    = undefined

typingsToType :: [Typing] -> Type
typingsToType [t     ] = typingToType t
typingsToType (t : xs) = TArr (typingToType t) (typingsToType xs)

typingToType :: Typing -> Type
typingToType (Typing t) | t == "Num"    = TCon CNum
                        | t == "Bool"   = TCon CBool
                        | t == "String" = TCon CString
                        | otherwise     = TVar $ TV t

initialEnv :: Env
initialEnv = Env
  { envvars = M.fromList
                [ ( "==="
                  , Forall [TV "a"]
                  $      TVar (TV "a")
                  `TArr` TVar (TV "a")
                  `TArr` TCon CBool
                  )
                , ("+", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
                , ("-", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
                , ("*", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
                , ("/", Forall [] $ TCon CNum `TArr` TCon CNum `TArr` TCon CNum)
                , ( "singleton"
                  , Forall [TV "a"] $ TArr (TVar $ TV "a") $ TComp
                    (CUserDef "List")
                    [TVar $ TV "a"]
                  )
                ]
  , envadts = M.empty
  }

buildInitialEnv :: AST -> Env
buildInitialEnv AST { aadts } =
  let tadts = buildADTTypes aadts
      vars  = M.union (envvars initialEnv) (resolveADTs tadts aadts)
  in  Env { envvars = vars, envadts = tadts }

buildADTTypes :: [ADT] -> ADTs
buildADTTypes adts = M.fromList $ buildADTType <$> adts

buildADTType :: ADT -> (String, Type)
buildADTType ADT { adtname, adtparams } =
  (adtname, TComp (CUserDef adtname) (TVar . TV <$> adtparams))

resolveADTs :: ADTs -> [ADT] -> Vars
resolveADTs tadts = M.fromList . (>>= resolveADT tadts)

resolveADT :: ADTs -> ADT -> [(String, Scheme)]
resolveADT tadts ADT { adtname, adtconstructors, adtparams } =
  resolveADTConstructor tadts adtname adtparams <$> adtconstructors

-- TODO: Still a lot of work here !
-- We need to be able to query resolved types to look up types using other subtypes in their constructors
-- Example:
-- data Result = Ok Some
-- data Some = Some String
-- For now just checking that the type exists should be enough
-- but when we add support for typed data types ( Maybe a, List a, ... )
-- we'll need to also check that variables are given.
resolveADTConstructor
  :: ADTs -> Name -> [Name] -> ADTConstructor -> (String, Scheme)
resolveADTConstructor tadts n params ADTConstructor { adtcname, adtcargs = [] }
  = (adtcname, Forall (TV <$> params) $ buildADTConstructorReturnType n params)
resolveADTConstructor tadts n params ADTConstructor { adtcname, adtcargs } =
  let allTypes =
          (nameToType <$> adtcargs) <> [buildADTConstructorReturnType n params]
      typeArray = foldr1 TArr allTypes
  in  (adtcname, Forall (TV <$> params) typeArray)
 where
  nameToType n
    | n == "String" = TCon CString
    | n == "Bool" = TCon CBool
    | n == "Num" = TCon CNum
    | isLower (head n) && (n `elem` params) = TVar $ TV n
    | isLower (head n) = TVar $ TV n
    | -- TODO: Err, that variable is not bound !
      otherwise = case M.lookup n tadts of
      Just a  -> a
      Nothing -> TCon $ CUserDef n

buildADTConstructorReturnType :: Name -> [Name] -> Type
-- buildADTConstructorReturnType tname [] = TCon $ CUserDef tname -- TODO: Should this also be a TComp ? Or TADT ?
buildADTConstructorReturnType tname tparams =
  TComp (CUserDef tname) $ TVar . TV <$> tparams

inferExps :: Env -> [Exp] -> Infer [Type]
inferExps env [exp   ] = (: []) . snd <$> infer env exp
inferExps env (e : xs) = do
  r <- infer env e
  let env' = case e of
        Assignment { ename } -> extendVars env (ename, Forall [] $ snd r)
        TypedExp { eexp = Var { ename } } ->
          extendVars env (ename, Forall [] $ snd r)
        _ -> env
  (\n -> snd r : n) <$> inferExps env' xs

runInfer :: AST -> Either InferError [Type]
runInfer ast = fst <$> runExcept
  (runStateT (inferExps initialEnv $ aexps ast) Unique { count = 0 })
  where initialEnv = trace (show $ buildInitialEnv ast) (buildInitialEnv ast)
