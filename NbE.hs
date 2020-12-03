import Prelude hiding ( lookup )
import Data.Map ( insert, Map )
import Utils ( lookupOrError )

-- Syntax
data Expr = ExpVar Name
          | ExpLam Name Expr
          | ExpApp Expr Expr

type Name = String

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam Name NormalForm

-- Expressions that can be reified (also normal forms)
data NeutralForm = NeVar Name
                 | NeApp NeutralForm NormalForm

-- Semantics
data V = Neutral NeutralForm 
       | Function (V -> V) 

-- Environment
type Env = Map Name V

-- Converts syntax to semantics
eval :: Expr -> Env -> V
eval (ExpVar x)   env = lookupOrError x env
eval (ExpLam x m) env = Function f where
        f :: V -> V
        f v = eval m env' where
            env' = insert x v env
eval (ExpApp m n) env = app (eval m env) (eval n env)
        
app :: V -> V -> V
app (Function f) v = f v    
app (Neutral n)  v = reflect (NeApp n (reify v))

reify :: V -> NormalForm
reify (Neutral n)  = NfNeutralForm n
-- ISSUE: Need fresh variables
-- TODO: replace "x" with fresh variable
reify (Function f) = NfLam "x" (reify (app (Function f) (reflect (NeVar "x"))))

reflect :: NeutralForm -> V
reflect = Neutral

{- 
    Why do we not need reflect in untyped version?
        eval doing reflection for us?
    Why do we not need reflect in intensional version?
        extentional vs intentional?
-}