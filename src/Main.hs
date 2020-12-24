{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns #-}
module Main where

import qualified Data.Map                      as M
import           GHC.IO                         ( )
import           Text.Show.Pretty               ( ppShow )
import           Control.Monad.Except           ( runExcept )
import           Control.Monad.State            ( StateT(runStateT) )
import           System.FilePath                ( takeDirectory )
import           System.Directory               ( canonicalizePath
                                                , createDirectoryIfMissing
                                                )
import           System.Exit
import           Utils.Path              hiding ( PathUtils(..) )
import           Parse.AST

import           Infer.Solve
import           Infer.Infer
import           Options.Applicative
import           Tools.CommandLineFlags
import           Tools.CommandLine
import           Compile.Core
import           Compile.Runner
import qualified AST.Solved                    as Slv
import qualified Explain.Format                as Explain
import qualified Tools.REPL                    as REPL
import           Control.Monad                  ( when )
import           System.Process
import           Control.Exception              ( try
                                                , SomeException
                                                )
import           System.Environment             ( setEnv
                                                , getEnv
                                                )
import           System.Environment.Executable  ( getExecutablePath )
import           System.IO                      ( hPutStrLn
                                                , stderr
                                                )
import           Coverage.Coverable             ( collectFromAST
                                                , isFunction
                                                , isLine
                                                , Coverable(..)
                                                )
import           Data.List                      ( isInfixOf
                                                , isPrefixOf
                                                )
import           Data.String.Utils


main :: IO ()
main = run =<< execParser opts

isCoverageEnabled :: IO Bool
isCoverageEnabled = do
  coverageEnv <- try $ getEnv "COVERAGE_MODE"
  case coverageEnv :: Either IOError String of
    Right "on" -> return True
    _          -> return False

run :: Command -> IO ()
run cmd = do
  coverage <- isCoverageEnabled

  case cmd of
    Compile entrypoint outputPath _ verbose debug bundle ->
      runCompilation entrypoint outputPath verbose debug bundle coverage

    Test entrypoint coverage -> runTests entrypoint coverage

    Install                  -> runPackageInstaller
    ReadEvalPrintLoop        -> REPL.readEvaluatePrintLoop


runCoverageInitialization :: FilePath -> Slv.Table -> IO ()
runCoverageInitialization rootPath table = do
  let filteredTable =
        M.filterWithKey (\path _ -> shouldBeCovered rootPath path) table
  let coverableFunctions = M.map collectFromAST filteredTable
  let generated = M.mapWithKey generateLCovInfoForAST coverableFunctions
  let lcovInfoContent    = rstrip $ unlines $ M.elems generated

  createDirectoryIfMissing True ".coverage"
  writeFile ".coverage/lcov.info" lcovInfoContent


runPackageInstaller :: IO ()
runPackageInstaller = do
  executablePath              <- getExecutablePath
  packageInstallerPath        <- try $ getEnv "PKG_INSTALLER_PATH"
  packageInstallerPathChecked <-
    case (packageInstallerPath :: Either IOError String) of
      Left _ -> do
        return $ takeDirectory executablePath <> "/package-installer.js"
      Right p -> return p

  callCommand $ "node " <> packageInstallerPathChecked

runTests :: String -> Bool -> IO ()
runTests entrypoint coverage = do
  executablePath        <- getExecutablePath
  testRunnerPath        <- try $ getEnv "TEST_RUNNER_PATH"
  testRunnerPathChecked <- case (testRunnerPath :: Either IOError String) of
    Left _ -> do
      return $ takeDirectory executablePath <> "/test-runner.js"
    Right p -> return p

  setEnv "MADLIB_PATH" executablePath
  when coverage $ do
    setEnv "COVERAGE_MODE" "on"
  testOutput <-
    try $ callCommand $ "node " <> testRunnerPathChecked <> " " <> entrypoint
  case (testOutput :: Either IOError ()) of
    Left  e -> putStrLn $ ppShow e
    Right a -> return ()

