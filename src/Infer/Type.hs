{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Type where

import qualified Data.Map                      as M
import           AST.Source                     ( Exp )
import           Text.Show.Pretty               ( ppShow )
import           Debug.Trace                    ( trace )


type Vars = M.Map String Scheme
type TypeDecls = M.Map String Type
type Imports = M.Map String Type

-- Instance:
--   Type:           type the instance handles
--   String:         The interface it instantiates
--   Map String Exp: The dictionary of exps from the instance
--   [String]:       The constraints on the instance ? Not clear yet.
data Instance = Instance Type String (M.Map String Exp) [String] deriving(Eq, Show)
type Instances = [Instance]

data Interface = Interface String String (M.Map String Type) deriving(Eq, Show)
type Interfaces = [Interface]


data Env
  = Env
    { envvars        :: Vars
    , envtypes       :: TypeDecls
    , envimports     :: Imports
    , envinterfaces  :: Interfaces
    , envinstances   :: Instances
    , envcurrentpath :: FilePath
    }
    deriving(Eq, Show)


data TVar = TV Id Kind
  deriving (Show, Eq, Ord)

data TCon = TC Id Kind
  deriving (Show, Eq, Ord)

data Type
  = TVar TVar          -- Variable type
  | TCon TCon                   -- Constructor type
  | TGen Int
  | TApp Type Type              -- Arrow type
  | TComp FilePath Id [Type]         -- Composite type
  | TRecord (M.Map Id Type) Bool -- Record type: Bool means open or closed
  | TAlias FilePath Id [TVar] Type -- Aliases, filepath of definition module, name, params, type it aliases
  | TTuple [Type]
  deriving (Show, Eq, Ord)

infixr `TApp`


tNumber :: Type
tNumber = TCon $ TC "Number" Star

tBool :: Type
tBool = TCon $ TC "Boolean" Star

tStr :: Type
tStr = TCon $ TC "String" Star

tUnit :: Type
tUnit = TCon $ TC "()" Star

tList :: Type
tList = TCon $ TC "List" (Kfun Star Star)

tArrow :: Type
tArrow = TCon $ TC "(->)" (Kfun Star (Kfun Star Star))

infixr      4 `fn`
fn :: Type -> Type -> Type
a `fn` b = TApp (TApp tArrow a) b



type Id = String

data Kind  = Star | Kfun Kind Kind
             deriving (Eq, Show, Ord)

data Pred   = IsIn Id [Type]
              deriving (Eq, Show, Ord)

data Qual t = [Pred] :=> t
              deriving (Eq, Show, Ord)

data Scheme = Forall [Kind] (Qual Type)
              deriving (Eq, Show, Ord)


type Substitution = M.Map TVar Type


qualType :: Qual t -> t
qualType (_ :=> t) = t

extractQualifiers :: [Qual t] -> ([Pred], [t])
extractQualifiers []         = ([], [])
extractQualifiers [ps :=> t] = (ps, [t])
extractQualifiers ((ps :=> t) : qs) =
  let (ps', ts') = extractQualifiers qs in (ps <> ps', t : ts')


class HasKind t where
  kind :: t -> Kind
instance HasKind TVar where
  kind (TV _ k) = k
instance HasKind TCon where
  kind (TC _ k) = k
instance HasKind Type where
  kind (TCon tc    ) = kind tc
  kind (TVar u     ) = kind u
  kind (TRecord _ _) = Star
  kind (TApp    t _) = case kind t of
    (Kfun _ k) -> k


-- Do we still need this ?
arrowReturnType :: Type -> Type
arrowReturnType (TApp _ (TApp y x)) = arrowReturnType (TApp y x)
arrowReturnType (TApp _ x         ) = x
arrowReturnType x                   = x
