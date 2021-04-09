
module Untyped.GensymNbE () where
import Prelude hiding ( lookup, empty )
import Data.Map (  insert, Map, mapKeys, lookup )
import qualified Data.Map as Map (empty) 

import Control.Monad.State ( MonadState(get), State, modify, evalState )
import Data.Set ( Set, singleton, delete, union, notMember )

import Untyped.Utils (getFreeVariables, getFreshVariableStream)
import Untyped.TypeDeclarations (Name, Expr(..)) 

-- State monad for generating fresh variable names
-- Fresh variables represented as a stream of variable names
type FreshName = State [Name]

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam Name NormalForm
    deriving (Read, Show)

-- Expressions that can be reified (also contain no reductions)
data NeutralForm = NeVar Name
                 | NeApp NeutralForm NormalForm
    deriving (Read, Show)

-- Semantics
data V = Neutral NeutralV
       | Function (V -> V)

data NeutralV = NeVVar Name
              | NeVApp NeutralV V

-- Environment
type Env = Map Name V

-- Core NbE

-- Converts epxression syntax to semantics
eval :: Expr -> Env -> V
eval (ExpVar x) env = case lookup x env of
        -- Bound variable, returns the semantic value bound to x in the environment
        Just y -> y

        -- Free variable, embed into semantics as is
        Nothing -> Neutral (NeVVar x)

eval (ExpLam var m) env = Function f where
    -- Semantic function interpretation of the lambda expression syntax
    f v = eval m env' where
        -- Defines a new environment where semantic input to function bound to var (for the body of the lambda)
        env' = insert var v env

eval (ExpApp m n) env = app (eval m env) (eval n env) 
    where
        -- Defines the application of semantic expressions
        app :: V -> V -> V
        -- Evaluates the semantic function f at v (ie evaluates redex)
        app (Function f) v = f v
        -- This justifies the used of NeutralV rather than NeutralForm
        -- NeApp constructor requires NormalForm rather than V
        -- Could use reify' to transform V -> NormalForm but reify' requires state so FreshName monad introduced to app
        -- Since eval calls app it would also require state
        app (Neutral n)  v = Neutral (NeVApp n v)

-- Converts a sematic representation of a term into it's associated normal form
reify' :: V -> FreshName NormalForm
reify' (Neutral n)  = do 
    reifiedN <- reifyNeutral' n
    return (NfNeutralForm reifiedN)
reify' (Function f) = do
    freshNames <- get
    -- Remove the first name from the freshNames stream
    let freshVar = head freshNames
    -- The first name is no longer fresh (we are abount to use it as a bound variable)
    -- Modify the state to remove the used variable name
    modify tail
    -- reify' the body of the semantic function when evaluated at the fresh bound variable
    normalForm <- reify' (f (Neutral (NeVVar freshVar)))
    return (NfLam freshVar normalForm)

-- Converts a sematic representation of a neutral form into its associated semantic form
reifyNeutral' :: NeutralV -> FreshName NeutralForm
reifyNeutral' (NeVVar i)   = return (NeVar i)
reifyNeutral' (NeVApp n m) = do
    reifiedNeutral <- reifyNeutral' n
    reifiedNormal  <- reify' m
    return (NeApp reifiedNeutral reifiedNormal) 

reify :: V -> [Name] -> NormalForm
reify (Neutral n)  freshVars = NfNeutralForm (reifyNeutral n freshVars)
    where 
        reifyNeutral :: NeutralV -> [Name] -> NeutralForm
        reifyNeutral (NeVVar i)   freshVars = NeVar i
        reifyNeutral (NeVApp n m) freshVars = NeApp reifiedN reifiedM
            where
                reifiedN = reifyNeutral n freshVars
                reifiedM = reify m freshVars
reify (Function f) (v:vs)   = NfLam v body
    where 
        body = reify (f (Neutral (NeVVar v))) vs
    
normalise :: Expr -> NormalForm
normalise exp = reify (eval exp Map.empty) freshNames
    where
        freshNames = (getFreshVariableStream . getFreeVariables) exp

normaliseToExpr' :: Expr -> Expr
normaliseToExpr' = normalToExpr . normalise'

-- 'reify reifies the semantic form into its canonical normal form
-- 'evalState' returns the normal form of exp at the initial state (the stream of initially fresh variables for exp) 
normalise' :: Expr -> NormalForm
normalise' exp = evalState (reify' (eval exp Map.empty)) freshNames 
    where
        -- Generates the fresh name stream for exp
        freshNames = (getFreshVariableStream . getFreeVariables) exp

normaliseToExpr :: Expr -> Expr
normaliseToExpr = normalToExpr . normalise

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
identity = ExpLam "x" (ExpVar "x")

k :: Expr
k = ExpLam "x" (ExpLam "y" (ExpVar "x"))

k1 :: Expr
k1 = ExpLam "x" (ExpLam "y" (ExpVar "y"))

omega :: Expr
omega = ExpApp (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x"))) (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x")))