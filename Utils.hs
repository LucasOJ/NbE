module Utils ( lookupOrError ) where

import Prelude hiding ( lookup )
import Data.Map ( Map, lookup )

-- Returns value from the Map if present
-- Otherwise terminates exectution
lookupOrError :: (Ord k, Show k) => k -> Map k a -> a
lookupOrError k m = case lookup k m of
        Just x -> x
        Nothing -> error (show k ++ " not in map")

