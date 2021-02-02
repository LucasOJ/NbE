import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )
import Utils ( lookupOrError )

import Control.Monad.State ( MonadState(get), State, modify, evalState )

type Name = Int

-- State monad for generating fresh variable names
type FreshName = State Name

-- Syntax
data Expr = ExpVar Name
          | ExpLam Name Expr
          | ExpApp Expr Expr
    deriving (Read, Show)

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam Name NormalForm
    deriving (Read, Show)

-- Expressions that can be reified (also contain no reductions)
data NeutralForm = NeVar Name
                 | NeApp NeutralForm NormalForm
    deriving (Read, Show)

-- Semantics
data V = Neutral NeutralForm
       | Function (V -> V)

-- Environment
type Env = Map Name V

-- Converts syntax to semantics
eval :: Expr -> Env -> FreshName V
eval (ExpVar x) env = return v where
    v = case lookup x env of
        -- Bound variable, returns the semantic value bound to x in the environment
        Just y -> y
        
        -- Free variable
        Nothing -> Neutral (NeVar x)
            
eval (ExpLam var m) env = do
    freshVar <- get
    -- Semantic function interpretation of the lambda expression syntax
    let f v = evalState (eval m env') freshVar where
            -- Defines a new environment where semantic input to function bound to var (for the body of the lambda)
            env' = insert var v env
    return (Function f)

eval (ExpApp m n) env = do
    evalM <- eval m env
    evalN <- eval n env
    app evalM evalN

-- Defines the application of semantic expressions
app :: V -> V -> FreshName V
-- Evaluates the semantic function f at v (ie evaluates redex)
app (Function f) v = return (f v)
-- If the application does not reduce, create a semantic application
-- Need to reify v since NeApp :: NeutralForm -> NormalForm -> NeutralForm
app (Neutral n)  v = do
    reifiedV <- reify v
    return (Neutral (NeApp n reifiedV))

-- Converts a sematic representation of a term into it's associated normal form
reify :: V -> FreshName NormalForm
reify (Neutral n)  = return (NfNeutralForm n)
reify (Function f) = do
    freshVar <- get
    -- Since we introduced a new bound variable the state is not longer fresh so increment it
    modify (+1)
    -- Reify the body of the semantic function when evaluated at the fresh bound variable
    normalForm <- reify (f (Neutral (NeVar freshVar)))
    return (NfLam freshVar normalForm)

reflect :: NeutralForm -> V
reflect = Neutral

normalise :: Expr -> Expr
normalise exp = normalToExpr $ evalState (eval exp empty >>= reify) 0

--- Display

normalToExpr :: NormalForm -> Expr
normalToExpr (NfNeutralForm n) = neutralToExp n
normalToExpr (NfLam var n) = ExpLam var (normalToExpr n)

neutralToExp :: NeutralForm -> Expr
neutralToExp (NeVar i) = ExpVar i
neutralToExp (NeApp n m) = ExpApp (neutralToExp n) (normalToExpr m)

--- Combinators

identity :: Expr
identity = ExpLam 0 (ExpVar 0)

k1 :: Expr
k1 = ExpLam 0 (ExpLam 1 (ExpVar 0))

k2 :: Expr
k2 = ExpLam 0 (ExpLam 1 (ExpVar 1))

omega :: Expr
omega = ExpApp (ExpLam 0 (ExpApp (ExpVar 0) (ExpVar 0))) (ExpLam 0 (ExpApp (ExpVar 0) (ExpVar 0)))