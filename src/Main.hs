{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts   #-}
module Main where

import           Prelude                 hiding ( readFile )
import qualified Data.Map                      as M
import           GHC.IO                         ( )
import           System.Environment             ( getArgs )
import           Text.Show.Pretty               ( ppShow )
import           AST                            (ASTTable,  ASTError(..)
                                                , buildASTTable
                                                , findAST
                                                )
import           Infer
import           Control.Monad.Except           ( runExcept )
import           Control.Monad.State            ( StateT(runStateT) )
import           Compile
import           Debug.Trace                    ( trace )
import Grammar
import System.FilePath (takeDirectory, replaceExtension)
import System.Directory (createDirectoryIfMissing)

main :: IO ()
main = do
  entrypoint <- head <$> getArgs
  astTable   <- buildASTTable entrypoint
  putStrLn $ ppShow astTable

  let entryAST    = astTable >>= flip findAST entrypoint
      resolvedASTTable = case (entryAST, astTable) of
        (Right ast, Right table) -> runExcept (runStateT (inferAST table ast) Unique { count = 0 })
        (_, _) -> Left $ UnboundVariable ""
      -- resolvedAST = case (entryAST, astTable) of
      --   (Left _, Left _) -> Left $ UnboundVariable ""
      --   (Right ast, Right _) ->
      --     trace (ppShow $ runEnv ast) (runEnv ast) >>= (`runInfer` ast)
      --    where
      --     runEnv x = fst
      --       <$> runExcept (runStateT (buildInitialEnv x) Unique { count = 0 })

  putStrLn $ "RESOLVED:\n" ++ ppShow resolvedASTTable

  case resolvedASTTable of
    Left  _   -> putStrLn "Err"
    Right (table, _) -> do
      build table
      putStrLn "compiled JS:"
      putStrLn $ concat $ compile <$> M.elems table


build :: ASTTable -> IO ()
build table = (head <$>) <$> mapM buildAST $ M.elems table


buildAST :: AST -> IO ()
buildAST ast@AST { apath = Just path } = do
  let outputPath = makeOutputPath path
  
  createDirectoryIfMissing True $ takeDirectory outputPath
  writeFile outputPath $ compile ast


makeOutputPath :: FilePath -> FilePath
makeOutputPath path = "./build/" <> replaceExtension path "mjs"
