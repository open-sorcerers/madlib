module AST.Source where

import qualified Data.Map                      as M

import           Explain.Meta


data AST =
  AST
    { aimports    :: [Import]
    , aexps       :: [Exp]
    , atypedecls  :: [TypeDecl]
    , ainterfaces :: [Interface]
    , ainstances  :: [Instance]
    , apath       :: Maybe FilePath
    }
    deriving(Eq, Show)

type Import = Meta Import_

-- The second FilePath parameter is the absolute path to that module
data Import_
  = NamedImport [Name] FilePath FilePath
  | DefaultImport Name FilePath FilePath
  deriving(Eq, Show)

-- TODO: Rename TypeDecl
data TypeDecl
  = ADT
      { adtname :: Name
      , adtparams :: [Name]
      , adtconstructors :: [Constructor]
      , adtexported :: Bool
      }
  | Alias
      { aliasname :: Name
      , aliasparams :: [Name]
      , aliastype :: Typing
      , aliasexported :: Bool
      }
    deriving(Eq, Show)

data Interface = Interface Constraints Name Name (M.Map Name Typing) deriving(Eq, Show)

data Instance = Instance Constraints Name Typing (M.Map Name Exp) deriving(Eq, Show)

data Constructor
  = Constructor Name [Typing]
  deriving(Eq, Show)


type Typing = Meta Typing_

type Constraints = [Typing]

data Typing_
  = TRSingle Name
  | TRComp Name [Typing]
  | TRArr Typing Typing
  | TRRecord (M.Map Name Typing)
  | TRTuple [Typing]
  | TRConstrained Constraints Typing -- List of constrains and the typing it applies to
  deriving(Eq, Show)


type Is = Meta Is_
data Is_ = Is Pattern Exp deriving(Eq, Show)


type Pattern = Meta Pattern_
data Pattern_
  = PVar Name
  | PAny
  | PCtor Name [Pattern]
  | PNum String
  | PStr String
  | PBool String
  | PCon Name
  | PRecord (M.Map Name Pattern)
  | PList [Pattern]
  | PTuple [Pattern]
  | PSpread Pattern
  deriving(Eq, Show)


data Field
  = Field (Name, Exp)
  | FieldSpread Exp
  deriving(Eq, Show)


data ListItem
  = ListItem Exp
  | ListSpread Exp
  deriving(Eq, Show)


type Exp = Meta Exp_

data Exp_ = LNum String
          | LStr String
          | LBool String
          | LUnit
          | Var Name
          | App Exp Exp Bool
          | Abs Name [Exp]
          | FieldAccess Exp Exp
          | Assignment Name Exp
          | Record [Field]
          | If Exp Exp Exp
          | Where Exp [Is]
          | Export Exp
          | TypedExp Exp Typing
          | ListConstructor [ListItem]
          | TupleConstructor [Exp]
          | JSExp String
          deriving(Eq, Show)

type Name = String


-- AST TABLE

type Table = M.Map FilePath AST

getImportAbsolutePath :: Import -> FilePath
getImportAbsolutePath imp = case imp of
  Meta _ _ (NamedImport   _ _ n) -> n
  Meta _ _ (DefaultImport _ _ n) -> n

getImportPath :: Import -> (Import, FilePath)
getImportPath imp@(Meta _ _ (NamedImport   _ p _)) = (imp, p)
getImportPath imp@(Meta _ _ (DefaultImport _ p _)) = (imp, p)

extractExp :: Exp -> Exp_
extractExp (Meta _ _ e) = e
