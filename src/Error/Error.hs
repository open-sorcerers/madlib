{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Error.Error where

import           Infer.Type
import           Explain.Reason


data InferError = InferError TypeError Reason deriving(Eq, Show)

data TypeError
  = InfiniteType TVar Type
  | UnboundVariable String
  | UnificationError Type Type
  | KindError Type Type
  | NoInstanceFound String Type
  | InterfaceAlreadyDefined String
  | InterfaceNotExisting String
  | MethodDoesNotMatchInterfaceType Type Type
  | AmbiguousType (TVar, [Pred])
  | ADTAlreadyDefined Type
  | UnknownType String
  | WrongSpreadType String
  | FieldNotExisting String
  | ImportNotFound String
  | GrammarError FilePath String
  | FatalError
  | ASTHasNoPath
  deriving (Show, Eq, Ord)

