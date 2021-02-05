import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )

import Control.Monad.State ( MonadState(get), State, modify, evalState )
import Data.Set ( Set, singleton, delete, union, notMember )

type Name = Int

-- Syntax
data Expr = ExpVar Name
          | ExpLam Expr
          | ExpApp Expr Expr
    deriving (Read, Show)

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam NormalForm
    deriving (Read, Show)

-- Expressions that can be reified (also contain no reductions)
data NeutralForm = NeVar Name
                 | NeApp NeutralForm NormalForm
    deriving (Read, Show)

-- Semantics
data V = Neutral NeutralV
       | Function (V -> V)

data NeutralV = NeVLevel Int
              | NeVApp NeutralV V

-- Environment
type Env = Map Name V

-- Core NbE

-- Converts epxression syntax to semantics
eval :: Env -> Expr -> V
eval env (ExpVar x) = case lookup x env of
        -- Bound variable, returns the semantic value bound to x in the environment
        Just y -> y

        -- Free variable, embed into semantics as is
        -- TODO: What to do with free variables?
        Nothing -> undefined

eval env (ExpLam m) = Function f where
        f :: V -> V
        f v = eval env' m where
            env' = insert 0 v (mapKeys (+1) env)

eval env (ExpApp m n) = app (eval env m) (eval env n)

-- Defines the application of semantic expressions
app :: V -> V -> V
-- Evaluates the semantic function f at v (ie evaluates redex)
app (Function f) v = f v
-- If the application does not reduce, create a semantic application
-- Need to reify v since NeApp :: NeutralForm -> NormalForm -> NeutralForm
app (Neutral m)  v = Neutral (NeVApp m v)

-- Converts a sematic representation of a term into it's associated normal form
reify :: Int -> V -> NormalForm
reify n (Function f) = NfLam (reify (n + 1) (f (Neutral (NeVLevel n))))
reify n (Neutral m)  = NfNeutralForm (reifyNeutral n m)

reifyNeutral :: Int -> NeutralV -> NeutralForm
reifyNeutral n (NeVLevel k) = NeVar (n - 1 - k)
reifyNeutral n (NeVApp p q) = NeApp (reifyNeutral n p) (reify n q)

normalise :: Expr -> Expr
normalise = normalToExpr . reify 0 . eval empty

--- Display

-- Converts normal forms back to the expression syntax
normalToExpr :: NormalForm -> Expr
normalToExpr (NfNeutralForm n) = neutralToExp n
normalToExpr (NfLam n) = ExpLam (normalToExpr n)

-- Converts neutral forms back to the expression syntax
neutralToExp :: NeutralForm -> Expr
neutralToExp (NeVar i) = ExpVar i
neutralToExp (NeApp n m) = ExpApp (neutralToExp n) (normalToExpr m)

--- Combinators

identity :: Expr
identity = ExpLam (ExpVar 0)

k1 :: Expr
k1 = ExpLam (ExpLam (ExpVar 1))

k2 :: Expr
k2 = ExpLam (ExpLam (ExpVar 0))

omega :: Expr
omega = ExpApp (ExpLam (ExpApp (ExpVar 0) (ExpVar 0))) (ExpLam (ExpApp (ExpVar 0) (ExpVar 0)))