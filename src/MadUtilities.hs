module MadUtilities
  ( tap
  , tapM
  )
where

import           Debug.Trace
import           Data.Maybe

tap :: Show a => String -> a -> a
tap tag x = trace (tag ++ ": " ++ show x) x

tapM :: (Functor f, Show s) => String -> f s -> f s
tapM tag x = (tap tag) <$> x
{- isomorphic
tapM tag x = fmap (tap tag) x
tapM tag x = mapM (return . tap tag) x
-}

