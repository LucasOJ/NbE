
{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
module Monotyped.TypeDeclarations () where 

-- TypeVariables
type TypeVariable = String

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
    Up :: NeutralExpr ctx ty -> V ctx ty

    -- TODO: CHECK THIS - other way around?

    Function :: V (arg ': ctx) result -> V ctx (Arrow arg result)

-- This def?
data V' :: [Ty] -> Ty -> * where
    Up' :: NeutralExpr ctx ty -> V' ctx ty
    Func :: (V'(arg ': ctx) result -> V' ctx (Arrow arg result)) -> V' ctx result 

isNormal :: NormalExpr '[] t -> Bool 
isNormal _ = True

exprToString :: Expr '[] t -> String
exprToString = exprToString'

exprToString' :: Expr ctx t -> String
exprToString' (Var _) = "Var"
exprToString' (Lam body) = "Lam ( " ++ exprToString' body ++ " )"
exprToString' (App m n ) = "App " ++ exprToString' m ++ " " ++ exprToString' n

-- TODO: How to represent environment and tie in with type environent in type?

eval :: Expr '[] t -> V '[] t
eval = undefined 

identity :: Expr ctx (Arrow a a)
identity = Lam (Var Head)

k1 :: Expr ctx (Arrow a (Arrow b a))
k1 = Lam (Lam (Var (Tail Head)))

k2 :: Expr ctx (Arrow a (Arrow b b))
k2 = Lam (Lam (Var Head))

--exprToString' :: Expr a t -> String