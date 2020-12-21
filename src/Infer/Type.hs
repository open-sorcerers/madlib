{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Infer.Type where

import qualified Data.Map                      as M
import AST.Source (Exp)


type Vars = M.Map String Scheme
type TypeDecls = M.Map String Type
type Imports = M.Map String Type

-- Instance:
--   Type:           type the instance handles
--   String:         The class it instantiates
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


newtype TVar = TV String
  deriving (Show, Eq, Ord)


data Type
  = TVar [String] TVar          -- Variable type
  | TCon TCon                   -- Constant type
  | TArr Type Type              -- Arrow type
  | TComp FilePath String [Type]         -- Composite type
  | TRecord (M.Map String Type) Bool -- Record type: Bool means open or closed
  | TAlias FilePath String [TVar] Type -- Aliases, filepath of definition module, name, params, type it aliases
  | TTuple [Type]
  deriving (Show, Eq, Ord)


data TCon
  = CString
  | CNum
  | CBool
  | CUnit
  deriving (Show, Eq, Ord)

number :: Type
number = TCon CNum

bool :: Type
bool = TCon CBool

str :: Type
str = TCon CString

unit :: Type
unit = TCon CUnit

infixr `TArr`


data Scheme = Forall [TVar] Type
  deriving (Show, Eq, Ord)


type Substitution = M.Map TVar Type


arrowReturnType :: Type -> Type
arrowReturnType (TArr _ (TArr y x)) = arrowReturnType (TArr y x)
arrowReturnType (TArr _ x         ) = x
arrowReturnType x                   = x
