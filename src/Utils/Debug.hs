module Utils.Debug where

import           Control.Monad                  ( when )
import           Data.Maybe
import           Debug.Trace                    ( trace )
import           Text.Show.Pretty               ( ppShow )
import           System.Environment
import           System.ReadEnvVar
import           Text.Read                      ( readMaybe )

-- |'xtrace' is a tagged log
xtrace :: (Show a) => String -> a -> a
xtrace s x = trace (s ++ " " <> ppShow x) x

-- |'inspect' is 'xtrace' with a transform
inspect :: (Show y) => String -> (x -> y) -> x -> x
inspect s fn x = trace (s ++ " " <> ppShow (fn x)) x

-- |'printWhen' is a conditional 'xtrace'
printWhen :: Show p => (p -> Bool) -> String -> p -> p
printWhen cond tag x | doPrint == True = xtrace tag x
                     | otherwise       = x
  where doPrint = cond x
