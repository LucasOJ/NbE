import Prelude hiding ( lookup, empty )
import Data.Map (empty,  insert, Map, mapKeys, lookup )
import Utils ( lookupOrError )

-- Syntax
data Expr = ExpVar Int
          | ExpLam Expr
          | ExpApp Expr Expr 
    deriving (Read, Show)

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam NormalForm
    deriving (Read, Show)

-- Expressions that can be reified (also normal forms)
data NeutralForm = NeVar Int
                 | NeApp NeutralForm NormalForm
    deriving (Read, Show)

-- Semantics
data V = Neutral NeutralForm 
       | Function (V -> V) 

-- Environment
type Env = Map Int V

-- Converts syntax to semantics
eval :: Expr -> Env -> V
eval (ExpVar x) env = lookupOrVariable x env
eval (ExpLam m) env = Function f where
        f :: V -> V
        f v = eval m env' where
            env' = insert 0 v (mapKeys (+1) env)
            -- ISSUE: Update environment with shifted de-bruijn index (doesn't quite work)

eval (ExpApp m n) env = app (eval m env) (eval n env)

-- ISSUE: Is this correct?
-- If a variable is in the environment - fetch it
-- Otherwise return reflected variable (base case)
lookupOrVariable :: Int -> Env-> V
lookupOrVariable k m = case lookup k m of
        Just x -> x
        Nothing -> reflect (NeVar k)
        -- + number of lambdas deep?
        
app :: V -> V -> V
app (Function f) v = f v    
app (Neutral n)  v = reflect (NeApp n (reify v))

reify :: V -> NormalForm
reify (Neutral n)  = NfNeutralForm n
reify (Function f) = NfLam (reify (app (Function f) (reflect (NeVar 0))))

reflect :: NeutralForm -> V
reflect = Neutral

normalise :: Expr -> Expr
normalise exp = normalToExpr $ reify $ eval exp empty

normalToExpr :: NormalForm -> Expr
normalToExpr (NfNeutralForm n) = neutralToExp n
normalToExpr (NfLam n) = ExpLam (normalToExpr n)

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


--- Debug

--normalise k1 WRONG
--k1 (ExpVar 3) (ExpVar 4) RIGHT

{- 
    Why do we not need reflect in untyped version?
        eval doing reflection for us?
    Why do we not need reflect in intensional version?
        extentional vs intentional?

-}