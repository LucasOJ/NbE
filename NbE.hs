import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )
import Utils ( lookupOrError )

-- Syntax
data Expr = ExpVar Int
          | ExpLam Int Expr
          | ExpApp Expr Expr 
    deriving (Read, Show)

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam Int NormalForm
    deriving (Read, Show)

-- Expressions that can be reified (subset of normal forms)
data NeutralForm = NeVar Int
            -- change to level not index
                 | NeApp NeutralForm NormalForm
    deriving (Read, Show)

-- Semantics
data V = Neutral NeutralForm 
       | Function (V -> V) 

-- Environment
type Env = Map Int V

type Context = (Env, Int)

-- Converts syntax to semantics
eval :: Expr -> Env -> Int -> (V, Int)
eval (ExpVar x) env freshVar = (v, freshVar) where 
    v = case lookup x env of
        Just y -> y
            -- Bound variable
        Nothing -> Neutral (NeVar x)
            -- Free variable
            -- should reflect into level?

eval (ExpLam var m) env freshVar = (Function f, freshVar) where
        f :: V -> V
        f v = fst $ eval m env' freshVar where
            env' = insert var v env
            -- under lambdaCount -> bound
            -- otherwise -> free

eval (ExpApp m n) env freshVar = app evalM evalN freshVar''
    where 
        (evalM, freshVar') = eval m env freshVar
        (evalN, freshVar'') = eval n env freshVar'
        
app :: V -> V -> Int -> (V, Int)
app (Function f) v freshVar = (f v, freshVar)
    -- Increase all indicies here, except one inserting?
app (Neutral n)  v freshVar = (Neutral (NeApp n reifiedV), freshVar') where
    (reifiedV, freshVar') = reify v freshVar
    -- Need to reify v since NeApp :: NeutralForm -> NormalForm -> NeutralForm

reify :: V -> Int -> (NormalForm, Int)
reify (Neutral n)  freshVar = (NfNeutralForm n, freshVar)
reify (Function f) freshVar = (NfLam freshVar nf, freshVar')
    where (nf, freshVar') = reify (f (Neutral (NeVar freshVar))) (freshVar + 1)
    -- Inserts bound variables here
    -- How to insert higher-level bound variables?

reflect :: NeutralForm -> V
reflect = Neutral

normalise :: Expr -> Expr
normalise exp = normalToExpr $ fst $ reify v freshVar where
    (v, freshVar) = eval exp empty 0 

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

--- Debug

-- normalise k1 WRONG
-- ISSUE: not renaming bound variables correctly

{- 
    Why do we not need reflect in untyped version?
        eval doing reflection for us?
    Why do we not need reflect in intensional version?
        extentional vs intentional?
    Can we only normalise closed expressions?

-}