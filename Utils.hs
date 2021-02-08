module Utils (  ) where
import Data.Set ( Set, singleton, delete, union, notMember, toList )
import TypeDeclarations
import qualified Data.Map as Map (Map, fromList, toList, lookup, insert, empty, mapKeys) 
import Data.Tuple (swap)

-- Evaluates the set of free variables given an expression
getFreeVariables :: Expr -> Set Name
getFreeVariables (ExpVar x) = singleton x
getFreeVariables (ExpLam x m) = delete x (getFreeVariables m)
getFreeVariables (ExpApp m n) = getFreeVariables m `union` getFreeVariables n

freeVariableMapping :: [Name] -> Map.Map Name Int
freeVariableMapping = Map.fromList . flip zip [0..]

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap = Map.fromList . map swap . Map.toList

getFreshVariableStream :: Set Name -> [Name]
getFreshVariableStream freeVars = [freshVariable i | i <- [0..], notMember (freshVariable i) freeVars] where
        freshVariable i = "x" ++ show i

exprToDeBruijnExpr :: Expr -> Map.Map Name Int -> DbExpr
exprToDeBruijnExpr (ExpVar x) context = maybe undefined DbVar (Map.lookup x context)
exprToDeBruijnExpr (ExpLam x m) context = DbLam (exprToDeBruijnExpr m context') where
        context' = Map.insert x 0 (fmap (+1) context)
exprToDeBruijnExpr (ExpApp m n) context = DbApp (exprToDeBruijnExpr m context) (exprToDeBruijnExpr n context)

deBruijnExprToExpr :: DbExpr -> Map.Map Int Name -> [Name] -> Expr 
deBruijnExprToExpr (DbVar x) context _              = maybe undefined ExpVar (Map.lookup x context)
deBruijnExprToExpr (DbLam m) context (freshVar:freshVarStream') = 
        ExpLam freshVar (deBruijnExprToExpr m context' freshVarStream') where
        context' = Map.insert 0 freshVar (Map.mapKeys (+1) context)
deBruijnExprToExpr (DbApp m n) context freshVarStream = 
        ExpApp (deBruijnExprToExpr m context freshVarStream) (deBruijnExprToExpr n context freshVarStream)

-- Debug

expr :: Expr
expr = ExpApp (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x0"))) (ExpLam "y" (ExpVar "x1"))

expr_fv :: Set Name
expr_fv = getFreeVariables expr

expr_fv_list :: [Name]
expr_fv_list = toList expr_fv

fv_map :: Map.Map Name Int
fv_map = freeVariableMapping expr_fv_list

dBExpr :: DbExpr 
dBExpr = exprToDeBruijnExpr expr fv_map

reverseFVMap :: Map.Map Int Name
reverseFVMap = invertMap fv_map

fresh_vars :: [Name]
fresh_vars = getFreshVariableStream expr_fv

expr' :: Expr 
expr' = deBruijnExprToExpr dBExpr reverseFVMap fresh_vars