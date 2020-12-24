module Tools.REPL where

import           Control.Monad
import           Control.Monad.Except           ( runExcept )
import           Control.Monad.State            ( StateT(runStateT) )
import           Error.Error
import           Explain.Reason
import           Infer.Env
import           Infer.Infer
import           Infer.Solve
import           Parse.AST
import           System.IO
import           Compile.Core
import           Text.Show.Pretty               ( ppShow )

read' :: IO String
read' = putStr "𝙈 >" >> hFlush stdout >> getLine

eval' :: String -> String
eval' code =
  let inferred = case buildAST "path" code of
        (Right ast) -> runEnv ast >>= (`runInfer` ast)
        _           -> Left $ InferError (UnboundVariable "") NoReason
  in  case inferred of
        Right x ->
          compile (CompilationConfig "/" "/repl.mad" "./build" False) x
        Left e -> ppShow e
 where
  runEnv x = fst <$> runExcept
    (runStateT (buildInitialEnv initialEnv x) Unique { count = 0 })

print' :: String -> IO ()
print' = putStrLn

readEvaluatePrintLoop :: IO ()
readEvaluatePrintLoop = do
  input <- read'
  unless (input == ":quit") $ print' (eval' input) >> readEvaluatePrintLoop
