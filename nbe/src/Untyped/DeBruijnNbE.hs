
module Untyped.DeBruijnNbE (normaliseDbExpr) where 
import Prelude hiding ( lookup, empty )
import Data.Map (  insert, Map, mapKeys, lookup, size)
import qualified Data.Map as Map ( fromList, empty )
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

data NeutralV = NeVFreeVar Int
              | NeVBoundVar Int
              | NeVApp NeutralV V

-- Environment
type Env = Map Int V

---- Core NbE Functions

-- Converts epxression syntax to semantics
eval ::  Env -> DbExpr -> V
eval env (DbVar x) = case lookup x env of
        -- Bound variable, returns the semantic value bound to x in the environment
        Just y -> y

        -- Free variable, embed into semantics as is
        -- TODO: What to do with free variables?
        Nothing -> Neutral (NeVFreeVar (x - size env))

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
reify n (Function f) = NfLam (reify (n + 1) (f (Neutral (NeVBoundVar n))))
reify n (Neutral m)  = NfNeutralForm (reifyNeutral n m)
    where
        -- Converts a sematic neutral into its associated sytactic neutral form
        reifyNeutral :: Int -> NeutralV -> NeutralForm
        -- Converts a semantic deBruijn level into a sytactic deBruijn variable
        reifyNeutral n (NeVFreeVar k)  = NeVar (n + k)
        reifyNeutral n (NeVBoundVar k) = NeVar (n - 1 - k)
        reifyNeutral n (NeVApp p q)    = NeApp (reifyNeutral n p) (reify n q)

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

normalise :: DbExpr -> NormalForm
normalise = reify 0 . eval initialEnv where
    initialEnv = Map.empty 

-- Normalises a deBruijn expression given that it contains n free variables
normaliseDbExpr :: DbExpr -> DbExpr
normaliseDbExpr = normalToExpr . normalise

-- Main NbE Function
-- Given a string-named expression, produces the string named normal form
normaliseExpr :: Expr -> Expr
normaliseExpr expr = (deBruijnExprToExpr indexToName freshVariableStream 
                  . normaliseDbExpr 
                  . exprToDeBruijnExpr nameToIndex) expr where

    freeVariables = getFreeVariables expr

    -- Needed for string-named to deBruijn conversion 
    nameToIndex = getFreeVariableMapping freeVariables
    
    -- Needed for deBruijn to string-named conversion
    indexToName = invertMap nameToIndex
    freshVariableStream = getFreshVariableStream freeVariables

--- Combinators

identity :: DbExpr 
identity = DbLam (DbVar 0)

k1 :: DbExpr 
k1 = DbLam (DbLam (DbVar 1))

k2 :: DbExpr 
k2 = DbLam (DbLam (DbVar 0))

omega :: Expr 
omega = ExpApp (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x"))) (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x")))