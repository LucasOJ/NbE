import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )
import Utils ( lookupOrError )

import Control.Monad.State ( MonadState(get), State, modify, evalState )
import Data.Set ( Set, singleton, delete, union, notMember )

type Name = Int

-- State monad for generating fresh variable names
-- Fresh variables represented as a stream of variable names
type FreshName = State [Name]

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

-- Evaluates the set of free variables given an expression
freeVariables :: Expr -> Set Name
freeVariables (ExpVar x) = singleton x
freeVariables (ExpLam x m) = delete x (freeVariables m)
freeVariables (ExpApp m n) = freeVariables m `union` freeVariables n

-- Lazily produces a stream of fresh names for an expression given its free variables
freshNameStream :: Set Name -> [Name]
freshNameStream freeVariables = [x | x <- [0..], notMember x freeVariables]

-- Core NbE

-- Converts epxression syntax to semantics
eval :: Expr -> Env -> FreshName V
eval (ExpVar x) env = return v where
    v = case lookup x env of
        -- Bound variable, returns the semantic value bound to x in the environment
        Just y -> y

        -- Free variable, embed into semantics as is
        Nothing -> Neutral (NeVar x)

eval (ExpLam var m) env = do
    freshNames <- get
    -- Semantic function interpretation of the lambda expression syntax
    let f v = evalState (eval m env') freshNames where
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
    freshNames <- get
    -- Remove the first name from the freshNames stream
    let freshVar = head freshNames
    -- The first name is no longer fresh (we are abount to use it as a bound variable)
    -- Modify the state to remove the used variable name
    modify tail
    -- Reify the body of the semantic function when evaluated at the fresh bound variable
    normalForm <- reify (f (Neutral (NeVar freshVar)))
    return (NfLam freshVar normalForm)

reflect :: NeutralForm -> V
reflect = Neutral

-- 'eval exp empty' evaluates the expression using the empty context into a semantic form shared by all beta-equivalent terms 
-- 'reify' reifies the semantic form into its canonical normal form
-- 'evalState' returns the normal form of exp at the initial state (the stream of initially fresh variables for exp) 
normalise :: Expr -> Expr
normalise exp = normalToExpr $ evalState (eval exp empty >>= reify) freshNames where
    -- Generates the fresh name stream for exp
    freshNames = (freshNameStream . freeVariables) exp

--- Display

-- Converts normal forms back to the expression syntax
normalToExpr :: NormalForm -> Expr
normalToExpr (NfNeutralForm n) = neutralToExp n
normalToExpr (NfLam var n) = ExpLam var (normalToExpr n)

-- Converts neutral forms back to the expression syntax
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