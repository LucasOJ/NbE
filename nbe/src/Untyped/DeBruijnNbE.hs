
module Untyped.DeBruijnNbE () where 
import Prelude hiding ( lookup, empty )
import Data.Map (  insert, Map, mapKeys, lookup)
import qualified Data.Map as Map ( fromList )
import Control.Monad.State ( MonadState(get), State, modify, evalState )
import Data.Set ( Set, singleton, delete, union, notMember, toList )
import qualified Data.Set as Set (size)
import Untyped.Utils
import Untyped.TypeDeclarations

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam NormalForm
    deriving (Read, Show)

-- Expressions that can be reified (also contain no reductions)
data NeutralForm = NeVar Int
                 | NeApp NeutralForm NormalForm
    deriving (Read, Show)

-- Semantics
data V = Neutral NeutralV
       | Function (V -> V)

data NeutralV = NeVLevel Int
              | NeVApp NeutralV V

-- Environment
type Env = Map Int V

---- Core NbE Functions

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

---- Conversion back to standard deBruijn term

-- Converts normal forms back to the deBruijn expression syntax
normalToExpr :: NormalForm -> DbExpr
normalToExpr (NfNeutralForm n) = neutralToExp n
normalToExpr (NfLam n) = DbLam (normalToExpr n)

-- Converts neutral forms back to the deBruijn expression syntax
neutralToExp :: NeutralForm -> DbExpr
neutralToExp (NeVar i) = DbVar i
neutralToExp (NeApp n m) = DbApp (neutralToExp n) (normalToExpr m)

---- Normalisation functions  

-- Normalises a deBruijn expression given that it contains n free variables
normaliseDbExpr :: Int -> DbExpr -> DbExpr
normaliseDbExpr n = normalToExpr . reify n . eval initialEnv where
    -- The first n deBruijn indicies correspond to the free variables
    -- Their semantic representation is the final n deBruijn levels 
    initialEnv = Map.fromList [(k, Neutral (NeVLevel (n - 1 - k))) | k <-[0..(n - 1)]] 

-- Main NbE Function
-- Given a string-named expression, produces the string named normal form
normalise :: Expr -> Expr
normalise expr = (deBruijnExprToExpr indexToName freshVariableStream 
                  . normaliseDbExpr n 
                  . exprToDeBruijnExpr nameToIndex) expr where

    freeVariables = getFreeVariables expr

    -- Needed for string-named to deBruijn conversion 
    nameToIndex = getFreeVariableMapping freeVariables

    -- Needed for normalisation of deBruijn terms
    n = Set.size freeVariables
    
    -- Needed for deBruijn to string-named conversion
    indexToName = invertMap nameToIndex
    freshVariableStream = getFreshVariableStream freeVariables

--- Combinators

identity :: Expr
identity = ExpLam "x" (ExpVar "x")

k1 :: Expr
k1 = ExpLam "x" (ExpLam "y" (ExpVar "x"))

k2 :: Expr
k2 = ExpLam "x" (ExpLam "y" (ExpVar "y"))

omega :: Expr
omega = ExpApp (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x"))) (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x")))