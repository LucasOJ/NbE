import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )
import Control.Monad.State ( MonadState(get), State, modify, evalState )
import Data.Set ( Set, singleton, delete, union, notMember )

import TypeDeclarations ( DbExpr(DbVar, DbApp, DbLam) )

type Name = Int

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
eval :: Env -> DbExpr -> V
eval env (DbVar x) = case lookup x env of
        -- Bound variable, returns the semantic value bound to x in the environment
        Just y -> y

        -- Free variable, embed into semantics as is
        -- TODO: What to do with free variables?
        Nothing -> undefined

eval env (DbLam m) = Function f where
        f :: V -> V
        f v = eval env' m where
            env' = insert 0 v (mapKeys (+1) env)

eval env (DbApp m n) = app (eval env m) (eval env n)

-- Defines the application of semantic expressions
app :: V -> V -> V
-- Evaluates the semantic function f at v (ie evaluates redex)
app (Function f) v = f v
-- If the application does not reduce, create a semantic application
-- Need to reify v since NeApp :: NeutralForm -> NormalForm -> NeutralForm
-- Key difference -> Don't need to reify here (just does structural application)
app (Neutral m)  v = Neutral (NeVApp m v)

-- Converts a sematic representation of a term into its associated normal form
reify :: Int -> V -> NormalForm
-- Reifies a function by evaluating the function at the nth dB level
-- We increment by 1 since n represents the maximum number of free variables (we have introduced a new one)
reify n (Function f) = NfLam (reify (n + 1) (f (Neutral (NeVLevel n))))
reify n (Neutral m)  = NfNeutralForm (reifyNeutral n m)

-- Converts a sematic neutral into its associated sytactic neutral form
reifyNeutral :: Int -> NeutralV -> NeutralForm
-- Converts a semantic deBruijn level into a sytactic deBruijn variable
reifyNeutral n (NeVLevel k) = NeVar (n - 1 - k)
reifyNeutral n (NeVApp p q) = NeApp (reifyNeutral n p) (reify n q)

normaliseDbExpr :: DbExpr -> DbExpr
normaliseDbExpr = normalToExpr . reify 0 . eval empty

--- Display

-- Converts normal forms back to the expression syntax
normalToExpr :: NormalForm -> DbExpr
normalToExpr (NfNeutralForm n) = neutralToExp n
normalToExpr (NfLam n) = DbLam (normalToExpr n)

-- Converts neutral forms back to the expression syntax
neutralToExp :: NeutralForm -> DbExpr
neutralToExp (NeVar i) = DbVar i
neutralToExp (NeApp n m) = DbApp (neutralToExp n) (normalToExpr m)

--- Combinators

identity :: DbExpr 
identity = DbLam (DbVar 0)

k1 :: DbExpr 
k1 = DbLam (DbLam (DbVar 1))

k2 :: DbExpr 
k2 = DbLam (DbLam (DbVar 0))

omega :: DbExpr 
omega = DbApp (DbLam (DbApp (DbVar 0) (DbVar 0))) (DbLam (DbApp (DbVar 0) (DbVar 0)))