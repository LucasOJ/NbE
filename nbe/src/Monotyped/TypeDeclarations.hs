
{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
module Monotyped.TypeDeclarations () where 

-- TypeVariables
type TypeVariable = String

-- Representation of monotypes
data Ty = TyVar TypeVariable | Ty :-> Ty


-- Represents proof that a value is in a list
data IsElem :: [a] -> a -> * where
    -- Can construct such a proof if the value is at the beginning of the list
    IsHead :: IsElem (x ': xs) x
    -- The proof is still valid is we prepend an element to the list
    InTail :: IsElem xs x -> IsElem (y ': xs) x


-- Syntactic typed DeBruijn expressions
-- Each of the values is a term, and its type contains the context and type of the term
data Expr :: [Ty] -> Ty -> * where
    -- Given a proof the type ty is in the context ctx we know it's a variable??
    Var :: IsElem ctx ty -> Expr ctx ty
    -- Given an expression and context, we can abstract out the first bound variable in the context to make a lambda
    Lam :: Expr (arg ': ctx) result -> Expr ctx (arg :-> result)
    -- Given an expression applied to a term of function type, we can apply the argument to the function
    App :: Expr ctx (arg :-> result) -> Expr ctx arg -> Expr ctx result 


-- https://www.seas.upenn.edu/~cis194/spring15/lectures/11-stlc.html

data Type :: * -> * where
    TVar   :: Type TypeVariable
    TArrow  :: Type a -> Type b -> Type (a -> b)

data Expr' :: * -> * where
    Var' :: String -> Type a -> Expr' a
    Lam' :: String -> Type a -> Expr' b -> Expr' (a -> b)
    App' :: Expr' (a -> b) -> Expr' a -> Expr' b