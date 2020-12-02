import Prelude hiding ( lookup )
import Data.Map ( insert, Map )
import Utils ( lookupOrError )

-- Syntax
data Expr = ExpVar Name
          | ExpLam Name Expr
          | ExpApp Expr Expr

type Name = String

-- Normal Form           
data NormalForm = NfNeutralForm NeutralForm
                | NfLam Name NormalForm

data NeutralForm = NeVar Name
                 | NeApp NeutralForm NormalForm

-- Environment
type Env = Map Name V

-- Semantics
data V = Neutral NeutralForm 
       | Function (V -> V) 

-- Converts syntax to semantics
eval :: Expr -> Env -> V
eval (ExpVar x)   env = lookupOrError x env
eval (ExpLam x m) env = Function f where
        f :: V -> V
        f y = eval m env' where
            -- ISSUE: Overwrites cause problems for captured variables
            -- (shouldn't be present anyway)
            env' = insert x y env

eval (ExpApp m n) env = app (eval m env) (eval n env) where
        app :: V -> V -> V
        app (Function f) v = f v    
        -- ISSUE: Need normal form of v so depenent on reify
        app (Neutral n)   v = Neutral (NeApp n (reify v))

-- TODO: Implement reify
reify :: V -> NormalForm
reify = undefined 