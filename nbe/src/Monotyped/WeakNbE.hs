{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
module Monotyped.WeakNbE () where
import Monotyped.TypeDeclarations
import Data.Map (Map)

data WeakExpr :: Ty -> * where
    -- Given a proof the type ty is in the context ctx we know it's a variable??
    WeakVar :: Int -> WeakExpr ty
    -- Given an expression and context, we can abstract out the first bound variable in the context to make a lambda
    -- TODO: where does arg come from?
    WeakLam :: WeakExpr result -> WeakExpr (Arrow arg result)
    -- Given an expression applied to a term of function type, we can apply the argument to the function
    WeakApp :: WeakExpr (Arrow arg result) -> WeakExpr arg -> WeakExpr result 

-- Target Syntax (Normal Forms)
-- What do typed normal forms look like?
data NormalExpr :: Ty -> * where
    NormalNeutral :: NeutralExpr ty -> NormalExpr ty
    NormalLam :: NormalExpr result -> NormalExpr (Arrow arg result)

data NeutralExpr :: Ty -> * where
    NeutralVar :: Int -> NeutralExpr ty
    NeutralApp :: NeutralExpr (Arrow arg result) -> NormalExpr arg -> NeutralExpr result

-- Semantics
data V :: Ty -> * where 
    Up :: NeutralV ty -> V ty
    -- Closure :: Expr ctx ty -> V ctx ty
    -- ?? Do we need an env here

    -- TODO: CHECK THIS
    Function :: (V arg -> V result) -> V (Arrow arg result)

data NeutralV :: Ty -> * where 
    -- Need to be element of context?
    NeutralVLevel :: Int -> NeutralV ty
    NeutralVApp :: NeutralV (Arrow arg result) -> V arg -> NeutralV result 

elemToIndex :: Elem xs x -> Int
elemToIndex Head     = 0
elemToIndex (Tail n) = 1 + elemToIndex n

eraseContext :: Expr ctx ty -> WeakExpr ty
eraseContext (Var elem) = WeakVar (elemToIndex elem)
eraseContext (Lam body) = WeakLam (eraseContext body)
eraseContext (App m n)  = WeakApp (eraseContext m) (eraseContext n) 

-- Environment
-- type Env = Map Int V
data Env :: * where 
    Empty :: Env
    Shift :: V ty -> Env -> Env

-- TODO: Figure out heterogeneous lookups, ty currently universally qunatified
-- Need proof in list at type
envLookup :: WeakExpr ty -> Env -> V ty
--envLookup 0 (Shift v _)   = v
--envLookup n (Shift _ env) = envLookup (n - 1) env

envLookup (WeakVar 0) (Shift v _)   = v

---- Core NbE Functions

-- Converts epxression syntax to semantics
eval :: Env -> WeakExpr ty -> V ty
eval env (WeakVar x) = envLookup x env

eval env (WeakLam m) = Function f where
        f v = eval env' m where
            env' = Shift v env

eval env (WeakApp m n) = app (eval env m) (eval env n)

-- Defines the application of semantic expressions
app :: V (Arrow a b) -> V a -> V b
-- Evaluates the semantic function f at v (ie evaluates redex)
app (Function f) v = f v
-- If the application does not reduce, create a semantic application
-- Need to reify v since NeApp :: NeutralForm -> NormalForm -> NeutralForm
-- Key difference -> Don't need to reify here (just does structural application)
app (Up m)  v = Up (NeutralVApp m v)

-- Converts a sematic representation of a term into its associated normal form
reify :: Int -> V ty -> NormalExpr ty
-- Reifies a function by evaluating the function at the nth dB level
-- We increment by 1 since n represents the maximum number of free variables (we have introduced a new one)
reify n (Function f) = NormalLam (reify (n + 1) (f (Up (NeutralVLevel n))))
reify n (Up m)  = NormalNeutral (reifyNeutral n m)

-- Converts a sematic neutral into its associated sytactic neutral form
reifyNeutral :: Int -> NeutralV ty -> NeutralExpr ty
-- Converts a semantic deBruijn level into a sytactic deBruijn variable
reifyNeutral n (NeutralVLevel k) = NeutralVar (n - 1 - k)
reifyNeutral n (NeutralVApp p q) = NeutralApp (reifyNeutral n p) (reify n q)

---- Conversion back to standard deBruijn term

-- Converts normal forms back to the deBruijn expression syntax
normalToExpr :: NormalExpr ty -> WeakExpr ty
normalToExpr (NormalNeutral n) = neutralToExp n
normalToExpr (NormalLam n) = WeakLam (normalToExpr n)

-- Converts neutral forms back to the deBruijn expression syntax
neutralToExp :: NeutralExpr ty -> WeakExpr ty
neutralToExp (NeutralVar i) = WeakVar i
neutralToExp (NeutralApp n m) = WeakApp (neutralToExp n) (normalToExpr m)

---- Normalisation functions  

-- Normalises a deBruijn expression given that it contains n free variables
normalise :: Expr '[] ty -> WeakExpr ty
normalise = normalToExpr . reify 0 . eval Empty . eraseContext