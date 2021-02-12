module Utils ( getFreeVariables, getFreeVariableMapping, invertMap, getFreshVariableStream, exprToDeBruijnExpr, deBruijnExprToExpr ) where
import Data.Set ( Set, singleton, delete, union, notMember, toList )
import TypeDeclarations
import qualified Data.Map as Map (Map, fromList, toList, lookup, insert, empty, mapKeys) 
import Data.Tuple (swap)

-- Evaluates the set of free variables given an expression
getFreeVariables :: Expr -> Set Name
getFreeVariables (ExpVar x) = singleton x
getFreeVariables (ExpLam x m) = delete x (getFreeVariables m)
getFreeVariables (ExpApp m n) = getFreeVariables m `union` getFreeVariables n

-- Given a set of free variables produces a map from free variable -> distinct int 
-- Bijection between set of free variables and [0..#freeVariables]
getFreeVariableMapping :: Set Name -> Map.Map Name Int
getFreeVariableMapping = Map.fromList . flip zip [0..] . toList

-- Swaps the keys and values of a Map
-- Given a bijection, finds the inverse
invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap = Map.fromList . map swap . Map.toList

-- Produces a stream of fresh variables 
-- All variable names in the stream don't collide with any free variables in the term to prevent variable capture
getFreshVariableStream :: Set Name -> [Name]
getFreshVariableStream freeVars = [freshVariable i | i <- [0..], notMember (freshVariable i) freeVars] where
        freshVariable i = "v" ++ show i

-- Given the mapping of free variables to deBruijn indexes, produce the deBruijn respresentation of a term
exprToDeBruijnExpr :: Map.Map Name Int -> Expr -> DbExpr
-- Technically this function could return undefined
-- Correctness guarentees that lookups are on peformed on names in the context
exprToDeBruijnExpr context (ExpVar x)   = maybe undefined DbVar (Map.lookup x context)
exprToDeBruijnExpr context (ExpLam x m) = DbLam (exprToDeBruijnExpr context' m) where
        -- Since we enter the body of a new lambda, the named variable maps to the 0th abstraction index in context'
        -- The rest of the mapped indicies are incremented by 1
        context' = Map.insert x 0 (fmap (+1) context)
exprToDeBruijnExpr context (ExpApp m n) = DbApp (exprToDeBruijnExpr context m) (exprToDeBruijnExpr context n)

-- Given the mapping of deBruijn indexes to freeVariables, produce the string-named representation of a term
deBruijnExprToExpr :: Map.Map Int Name -> [Name] -> DbExpr -> Expr
-- Technically this function could return undefined
-- Correctness guarentees that lookups are on peformed on indicies in the context
deBruijnExprToExpr context _                          (DbVar x)   = maybe undefined ExpVar (Map.lookup x context)
deBruijnExprToExpr context (freshVar:freshVarStream') (DbLam m)   = 
        ExpLam freshVar (deBruijnExprToExpr context' freshVarStream' m) where
        -- Performs the same transformation as the exprToDeBruijnExpr lambda case
        -- However in this case the keys and values have swapped since we are considering the bijection in the other direction
        context' = Map.insert 0 freshVar (Map.mapKeys (+1) context)
-- It is ok to "split" freshVarStream here as the bound variables of each subterm are indepdendent 
deBruijnExprToExpr context freshVarStream             (DbApp m n) = 
        ExpApp (deBruijnExprToExpr context freshVarStream m) (deBruijnExprToExpr context freshVarStream n)

-- Debug

expr :: Expr
expr = ExpApp (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x0"))) (ExpLam "y" (ExpVar "x1"))