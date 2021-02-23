
{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
module Monotyped.TypeDeclarations () where 


-- Representation of monotypes
data Ty = BaseTy | Arrow Ty Ty

-- Represents proof that a value is in a list
data Elem :: [a] -> a -> * where
    -- Can construct such a proof if the value is at the beginning of the list
    Head :: Elem (x ': xs) x
    -- The proof is still valid is we prepend an element to the list
    Tail :: Elem xs x -> Elem (y ': xs) x

-- Syntactic typed DeBruijn expressions
-- Each of the values is a term, and its type contains the context and type of the term
data Expr :: [Ty] -> Ty -> * where
    -- Given a proof the type ty is in the context ctx we know it's a variable??
    Var :: Elem ctx ty -> Expr ctx ty
    -- Given an expression and context, we can abstract out the first bound variable in the context to make a lambda
    Lam :: Expr (arg ': ctx) result -> Expr ctx (Arrow arg result)
    -- Given an expression applied to a term of function type, we can apply the argument to the function
    App :: Expr ctx (Arrow arg result) -> Expr ctx arg -> Expr ctx result 

-- Target Syntax (Normal Forms)
-- What do typed normal forms look like?
data NormalExpr :: [Ty] -> Ty -> * where
    NormalNeutral :: NeutralExpr ctx ty -> NormalExpr ctx ty
    NormalLam :: NormalExpr (arg ': ctx) result -> NormalExpr ctx (Arrow arg result)

data NeutralExpr :: [Ty] -> Ty -> * where
    NeutralVar :: Elem ctx ty -> NeutralExpr ctx ty

    -- TODO: CHECK THIS
    NeutralApp :: NeutralExpr ctx (Arrow arg result) -> NormalExpr ctx arg -> NeutralExpr ctx result

-- Semantics
data V :: [Ty] -> Ty -> * where 
    Up :: NeutralV ctx ty -> V ctx ty

    -- TODO: CHECK THIS
    Function :: (V ctx arg -> V (arg ': ctx) result) -> V ctx (Arrow arg result)

data NeutralV :: [Ty] -> Ty -> * where 
    -- Need to be element of context?
    NeutralVVar :: Elem ctx ty -> NeutralV ctx ty
    NeutralVApp :: NeutralV ctx (Arrow arg result) -> V ctx arg -> NeutralV ctx result 


data Env :: [Ty] -> * where
    Empty :: Env '[]
    Shift :: V ctx ty -> Env types -> Env (ty : types)

-- ty should remain the same always
eval' :: Env ctx -> Expr ctx ty -> V ctx ty
eval' env (Var elemProof) = undefined 
eval' env (Lam body) = Function f where
    f v = eval' env' body where
        env' = Shift v env
eval' env (App m n) = app (eval' env m) (eval' env n) 

app :: V ctx (Arrow arg result) -> V ctx arg -> V ctx result 
app (Function f) v = f v
-- Do we need this case? Non-function appliation possible in typed lambda calc
app (Up m) n = Up (NeutralVApp m n) 

reify :: V ctx t -> NormalExpr ctx t
reify (Function f) = undefined 
reify (Up m) = undefined 

reifyNeutral :: NeutralV ctx t -> NeutralExpr ctx t
reifyNeutral (NeutralVVar elemProof) = undefined 
reifyNeutral (NeutralVApp m n) = NeutralApp (reifyNeutral m) (reify n)

--- Debug
eval :: Expr '[] t -> V '[] t
eval = undefined 

isNormal :: NormalExpr '[] t -> Bool 
isNormal _ = True

exprToString :: Expr '[] t -> String
exprToString = exprToString'

exprToString' :: Expr ctx t -> String
exprToString' (Var _) = "Var"
exprToString' (Lam body) = "Lam ( " ++ exprToString' body ++ " )"
exprToString' (App m n) = "App " ++ exprToString' m ++ " " ++ exprToString' n

-- TODO: How to represent environment and tie in with type environent in type?

elemToIndex :: Elem xs s -> Int
elemToIndex Head = 0
elemToIndex (Tail n) = 1 + elemToIndex n

--- Combinators

identity :: Expr ctx (Arrow a a)
identity = Lam (Var Head)

k1 :: Expr ctx (Arrow a (Arrow b a))
k1 = Lam (Lam (Var (Tail Head)))

k2 :: Expr ctx (Arrow a (Arrow b b))
k2 = Lam (Lam (Var Head))

--exprToString' :: Expr a t -> String