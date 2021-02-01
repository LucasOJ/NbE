import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )
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
eval :: Expr -> Context -> V
eval (ExpVar x) (env, _) = case lookup x env of
        Just x -> x
            -- Bound variable
        Nothing -> undefined
            -- Free variable
            -- should reflect into level?

eval (ExpLam m) (env, absDepth) = Function f where
        f :: V -> V
        f v = eval m context' where
            context' = (insert 0 v (mapKeys (+1) env), absDepth + 1)
            -- under lambdaCount -> bound
            -- otherwise -> free

eval (ExpApp m n) context = app (eval m context) (eval n context)
        
app :: V -> V -> V
app (Function f) v = f v
    -- Increase all indicies here, except one inserting?
app (Neutral n)  v = Neutral (NeApp n (reify v))
    -- Need to reify v since NeApp :: NeutralForm -> NormalForm -> NeutralForm

reify :: V -> NormalForm
reify (Neutral n)  = NfNeutralForm n
reify (Function f) = NfLam (reify (f (Neutral (NeVar 0))))
    -- Inserts bound variables here
    -- How to insert higher-level bound variables?

reflect :: NeutralForm -> V
reflect = Neutral


normalise :: Expr -> Expr
normalise exp = normalToExpr $ reify $ eval exp (empty, 0)

--- Display

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

-- normalise k1 WRONG
-- ISSUE: not renaming bound variables correctly

{- 
    Why do we not need reflect in untyped version?
        eval doing reflection for us?
    Why do we not need reflect in intensional version?
        extentional vs intentional?
    Can we only normalise closed expressions?

-}