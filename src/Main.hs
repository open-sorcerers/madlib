{-# LANGUAGE FlexibleContexts   #-}
module Main where

import qualified Data.Map                      as M
import           GHC.IO                         ( )
import           System.Environment             (getEnv,  getArgs )
import           Text.Show.Pretty               ( ppShow )
import           Control.Monad.Except           ( runExcept )
import           Control.Monad.State            ( StateT(runStateT) )
import           System.FilePath                ( takeDirectory
                                                , replaceExtension
                                                )
import           System.Directory               ( createDirectoryIfMissing )
import           System.Process
import           Path
import           AST

import           Infer.Solve
import           Infer.Infer
import           Compile
import qualified AST.Solved                    as Slv
import qualified Explain.Format                as Explain
import Control.Exception (SomeException, try)
import GHC.IO.Exception (ExitCode)


main :: IO ()
main = do
  entrypoint <- head <$> getArgs
  astTable   <- buildASTTable entrypoint
  putStrLn $ ppShow astTable

  let rootPath = computeRootPath entrypoint

  let entryAST         = astTable >>= flip findAST entrypoint
      resolvedASTTable = case (entryAST, astTable) of
        (Right ast, Right table) -> runExcept
          (runStateT (inferAST rootPath table ast) Unique { count = 0 })
        (_, Left e) -> Left e

  putStrLn $ "RESOLVED:\n" ++ ppShow resolvedASTTable

  case resolvedASTTable of
    Left  err        -> Explain.format readFile err >>= putStrLn
    Right (table, _) -> do
      generate table
      putStrLn "compiled JS:"
      putStrLn $ concat $ compile <$> M.elems table

  let bundleName = "bundle.js"

  bundled <- bundle bundleName entrypoint
  case bundled of
    Left e -> putStrLn e
    _      -> return ()


rollupNotFoundMessage = unlines 
  [ "Compilation error:"
  , "Rollup was not found."
  , "You must have rollup installed in order to use the bundling option. Please visit this page in order to install it: https://rollupjs.org/guide/en/#installation"
  ]

bundle :: FilePath -> FilePath -> IO (Either String ())
bundle dest entrypoint = do
  rollupPath <- try $ getEnv "ROLLUP_PATH"
  rollupPathChecked <- case (rollupPath :: Either IOError String) of
        Left _ -> do
          r <- try (readProcessWithExitCode "rollup" ["--version"] "") :: IO (Either SomeException (ExitCode, String, String))
          case r of
            Left _  -> return $ Left rollupNotFoundMessage
            Right _ -> return $ Right "rollup"
        Right p -> do
          r <- try (readProcessWithExitCode p ["--version"] "") :: IO (Either SomeException (ExitCode, String, String))
          case r of
            Left _ -> do
              r <- try (readProcessWithExitCode "rollup" ["--version"] "") :: IO (Either SomeException (ExitCode, String, String))
              case r of
                Left _ -> return $ Left rollupNotFoundMessage
                Right _   -> return $ Right "rollup"
            Right _ -> return $ Right p

  let entrypointOutputPath = makeOutputPath entrypoint
  let bundleOutputPath = takeDirectory entrypointOutputPath <> "/" <> dest

  case rollupPathChecked of
    Right rollup -> do
      (exitCode, stdout, stderr) <- readProcessWithExitCode rollup [entrypointOutputPath, "--file", bundleOutputPath] ""
      return $ Right ()
    Left e -> return $ Left e


generate :: Slv.Table -> IO ()
generate table = (head <$>) <$> mapM generateAST $ M.elems table


generateAST :: Slv.AST -> IO ()
generateAST ast@Slv.AST { Slv.apath = Just path } = do
  let outputPath = makeOutputPath path

  createDirectoryIfMissing True $ takeDirectory outputPath
  writeFile outputPath $ compile ast


makeOutputPath :: FilePath -> FilePath
makeOutputPath path = "./build/" <> replaceExtension path "mjs"

