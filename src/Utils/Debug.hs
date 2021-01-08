module Utils.Debug where

import           Control.Monad                  ( when )
import           Data.Maybe
import           Debug.Trace                    ( trace )
import           Text.Show.Pretty               ( ppShow )
import           System.Environment
import           System.ReadEnvVar
import           Text.Read                      ( readMaybe )

xtrace :: (Show a) => String -> a -> a
xtrace s x = trace (s ++ " " <> ppShow x) x

-- instance Show a => Show String a where
--   xtrace s x = trace (s ++ " " <> ppShow x) x

inspect :: (Show y) => String -> (x -> y) -> x -> x
inspect s fn x = trace (s ++ " " <> ppShow (fn x)) x

printWhen :: Show p => (p -> Bool) -> String -> p -> p
printWhen cond tag x | doPrint == True = xtrace tag x
                     | otherwise       = x
  where doPrint = cond x

-- printWhenEnv :: (Show x) => String -> x -> x

-- printWhenEnv envkey x = do
--   f <- lookupEnvDef envkey "NOT_SET"
--   return (xtrace envkey <$> f)
  
printWhenEnv envkey x = do
  f <- lookupEnvDef envkey "NOT_SET"
  return (xtrace envkey <$> f)
  
