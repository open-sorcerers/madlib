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
  | NoInstanceFound String Type
  | ADTAlreadyDefined Type
  | UnknownType String
  | WrongSpreadType String
  | FieldNotExisting String
  | ImportNotFound String
  | GrammarError FilePath String
  | FatalError
  | ASTHasNoPath
  deriving (Show, Eq, Ord)

