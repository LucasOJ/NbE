
{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
module Monotyped.TypeDeclarations (
    Ty(..),
    Elem(..),
    Expr(..)
) where 

--import GHC.Types

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
    NeutralApp :: NeutralExpr ctx (Arrow arg result) -> NormalExpr ctx arg -> NeutralExpr ctx result

-- Semantics
data V :: [Ty] -> Ty -> * where 
    Up :: NeutralV ctx ty -> V ctx ty
    -- Closure :: Expr ctx ty -> V ctx ty
    -- ?? Do we need an env here

    -- TODO: CHECK THIS
    Function :: (V ctx arg -> V ctx result) -> V ctx (Arrow arg result)

data NeutralV :: [Ty] -> Ty -> * where 
    -- Need to be element of context?
    NeutralVVar :: Elem ctx ty -> NeutralV ctx ty
    NeutralVApp :: NeutralV ctx (Arrow arg result) -> V ctx arg -> NeutralV ctx result 


data Env :: [Ty] -> * where
    Empty :: Env '[]
    Shift :: V (ty : ctx) ty -> Env ctx -> Env (ty : ctx)

    -- Should we only add V into Env of same context?
    -- Yes -> only add v into same current context

-- Since ty is an element of types, we will never call on the empty environment
-- Need proof in env rather than proof in context

envLookup :: Elem types ty -> Env types -> V types ty 
envLookup Head     (Shift v _)   = v
envLookup (Tail n) (Shift _ env) = weaken (envLookup n env)

weaken :: V ctx t -> V (a ': ctx) t
weaken = undefined 


{-
data Env :: [Ty] -> * where 
    Empty :: Env '[]
    Shift :: V ctx ty -> Env ctx -> Env (ty : ctx)

envLookup :: Elem types ty -> Env types -> V types' ty
envLookup Head     (Shift v _ )  = v
envLookup (Tail n) (Shift _ env) = envLookup n env  


data FinOrd :: GHC.Types.Nat -> * where
    Zero :: FinOrd n
    Succ :: FinOrd n -> FinOrd (n'+1)
-}