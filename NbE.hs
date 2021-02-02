import Prelude hiding ( lookup, empty )
import Data.Map ( empty,  insert, Map, mapKeys, lookup )
import Utils ( lookupOrError )

type Name = Int

type NameState a = Name -> (a, Name)

-- Syntax
data Expr = ExpVar Name
          | ExpLam Name Expr
          | ExpApp Expr Expr 
    deriving (Read, Show)

-- Expressions with no reductions
data NormalForm = NfNeutralForm NeutralForm
                | NfLam Name NormalForm
    deriving (Read, Show)

-- Expressions that can be reified (subset of normal forms)
data NeutralForm = NeVar Name
                 | NeApp NeutralForm NormalForm
    deriving (Read, Show)

-- Semantics
data V = Neutral NeutralForm 
       | Function (V -> V) 

-- Environment
type Env = Map Name V

type Context = (Env, Name)

-- Converts syntax to semantics
eval :: Expr -> Env -> NameState V
eval (ExpVar x) env freshVar = (v, freshVar) where 
    v = case lookup x env of
        Just y -> y
            -- Bound variable
        Nothing -> Neutral (NeVar x)
            -- Free variable

eval (ExpLam var m) env freshVar = (Function f, freshVar) where
        f :: V -> V
        f v = fst $ eval m env' freshVar where
            env' = insert var v env

eval (ExpApp m n) env freshVar = app evalM evalN freshVar''
    where 
        (evalM, freshVar') = eval m env freshVar
        (evalN, freshVar'') = eval n env freshVar'
        
app :: V -> V -> NameState V
app (Function f) v freshVar = (f v, freshVar)
app (Neutral n)  v freshVar = (Neutral (NeApp n reifiedV), freshVar') where
    (reifiedV, freshVar') = reify v freshVar
    -- Need to reify v since NeApp :: NeutralForm -> NormalForm -> NeutralForm

reify :: V -> NameState NormalForm
reify (Neutral n)  freshVar = (NfNeutralForm n, freshVar)
reify (Function f) freshVar = (NfLam freshVar nf, freshVar')
    where (nf, freshVar') = reify (f (Neutral (NeVar freshVar))) (freshVar + 1)

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

omega :: Expr
omega = ExpApp (ExpLam 0 (ExpApp (ExpVar 0) (ExpVar 0))) (ExpLam 0 (ExpApp (ExpVar 0) (ExpVar 0)))

--- Debug


{- 
    extentional vs intentional?
-}