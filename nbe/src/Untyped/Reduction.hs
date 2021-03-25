module Untyped.Reduction () where 
import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )

import Untyped.TypeDeclarations

type Env = Map Name Expr

normalise :: Env -> Expr -> Expr 

-- Evaluate redex (evaluate body in extended context)
normalise env (ExpApp (ExpLam x body) m) = normalise env' body 
    where
        env' = insert x m env

normalise env (ExpVar x) = case lookup x env of
    -- Normalise after substituting variable
    Just y -> normalise env y
    -- Free variables cannot be reduced
    Nothing -> ExpVar x

normalise env (ExpLam x body) = ExpLam x (normalise env body)

normalise env (ExpApp m n) | isRedex expr' = normalise env expr'
                            -- Evalulating inside and App may introduce a new redex

                           | otherwise = expr'
    where
        expr' = ExpApp (normalise env m) (normalise env n)

        isRedex :: Expr -> Bool
        isRedex (ExpApp (ExpLam _ _) _) = True 
        isRedex _                       = False