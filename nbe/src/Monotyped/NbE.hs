{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}

{-# LANGUAGE StandaloneDeriving #-}
module Monotyped.NbE (
    Ty(..),
    Elem(..),
    Expr(..),
    ClosedExpr,
    normalise,
    normaliseDB,
    normalToDB,
    SingTy
) where 

import Control.DeepSeq
import GHC.Generics (Generic)

import qualified Untyped.TypeDeclarations as Untyped (DbExpr(..), Expr(..))

-- Representation of monotypes
data Ty = BaseTy | Ty :-> Ty 
    deriving (Show)
infixr 9 :->

-- Represents proof that a value is in a list
data Elem :: [a] -> a -> * where
    -- Can construct such a proof if the value is at the beginning of the list
    Head :: Elem (x ': xs) x
    -- The proof is still valid is we prepend an element to the list
    Tail :: Elem xs x -> Elem (y ': xs) x

deriving instance (Show (Elem ctx ty))
deriving instance (Eq (Elem ctx ty))

-- Syntactic typed DeBruijn expressions
-- Each of the values is a term, and its type contains the typing context and type of the term
data Expr :: [Ty] -> Ty -> * where
    -- Given a proof the type ty is in the context ctx we know it's a variable
    Var :: Elem ctx ty -> Expr ctx ty
    -- Given an expression and context, we can abstract out the first bound variable in the context to make a lambda
    Lam :: (SingTy arg) => Expr (arg ': ctx) result -> Expr ctx (arg :-> result)
    -- Given an expression applied to a term of function type, we can apply the argument to the function
    App :: Expr ctx (arg :-> result) -> Expr ctx arg -> Expr ctx result 

deriving instance (Show (Expr ctx ty))

type ClosedExpr ty = Expr '[] ty

-- Target Syntax (Normal Forms)
-- Mirrors Expr other than that you can't apply a term to a Lambda
data NormalForm :: [Ty] -> Ty -> * where
    NormalNeutral :: NeutralForm ctx ty -> NormalForm ctx ty
    NormalLam     :: NormalForm (arg ': ctx) result -> NormalForm ctx (arg :-> result)

data NeutralForm :: [Ty] -> Ty -> * where
    NeutralVar :: Elem ctx ty -> NeutralForm ctx ty
    NeutralApp :: NeutralForm ctx (arg :-> result) -> NormalForm ctx arg -> NeutralForm ctx result

-- Semantics

-- Order Preserving Embeddings
-- Relation on typing contexts, OPE A B iff A contains B as a subsequence (ie B is embedded in A)
-- For any term m, m typeable with context B => m typeable with context A (since A is a stronger context than B)
-- A value of OPE A B is a proof that B is embedded in A (speicifies how to derive B from A)
data OPE :: [Ty] -> [Ty] -> * where
    Empty :: OPE '[] '[]
    Drop  :: OPE ctx1 ctx2 -> OPE (x : ctx1) ctx2
    Keep  :: OPE ctx1 ctx2 -> OPE (x : ctx1) (x : ctx2)

strengthenElem :: OPE strong weak -> Elem weak ty -> Elem strong ty
strengthenElem (Drop ope) v        = Tail (strengthenElem ope v)
strengthenElem (Keep ope) Head     = Head
strengthenElem (Keep ope) (Tail v) = Tail (strengthenElem ope v)

strengthenNormal :: OPE strong weak -> NormalForm weak ty -> NormalForm strong ty
strengthenNormal ope (NormalNeutral n) = NormalNeutral (strengthenNeutral ope n)
strengthenNormal ope (NormalLam n)     = NormalLam (strengthenNormal (Keep ope) n)

strengthenNeutral :: OPE strong weak -> NeutralForm weak ty -> NeutralForm strong ty
strengthenNeutral ope (NeutralVar n)   = NeutralVar (strengthenElem ope n)
strengthenNeutral ope (NeutralApp f n) = NeutralApp (strengthenNeutral ope f) (strengthenNormal ope n) 

composeOPEs :: OPE b c -> OPE a b -> OPE a c
composeOPEs v        Empty    = v
composeOPEs v        (Drop u) = Drop (composeOPEs v u)
composeOPEs (Drop v) (Keep u) = Drop (composeOPEs v u)
composeOPEs (Keep v) (Keep u) = Keep (composeOPEs v u)

data V :: [Ty] -> Ty -> * where 
    Base :: NormalForm ctx BaseTy -> V ctx BaseTy
    -- Values with type BaseTy are normal forms

    Function :: (SingContext ctx, SingTy arg) => 
        (forall ctx' . (SingContext ctx') => OPE ctx' ctx -> V ctx' arg -> V ctx' result) 
        -- Quantifies over all contexts containing 'weak'
        -- Requires Rank2Types
        -> V ctx (arg :-> result)
    -- Values with a function type a -> b are a semantic function from a -> b in any context stronger than that of the value 
    
strengthenV :: (SingContext strong) => OPE strong weak -> V weak ty -> V strong ty
strengthenV ope                      (Base nf) = Base (strengthenNormal ope nf)
strengthenV (ope :: OPE strong weak) (Function (f :: forall strong . (SingContext strong) => OPE strong weak -> V strong arg -> V strong result)) = Function f' 
    where
        f' :: (SingContext stronger) => OPE stronger strong -> V stronger arg -> V stronger result
        f' ope' = f (composeOPEs ope ope')

-- Semantic environment for evaluation
-- First typing context is for syntax (grows bigger as evaluate abstractions and more variables bound)
-- Second typing context is for the semantic terms
data Env :: [Ty] -> [Ty] -> * where
    EmptyEnv :: Env '[] ctxV
    ConsEnv  :: Env ctx ctxV -> V ctxV ty -> Env (ty : ctx) ctxV


strengthenEnv :: (SingContext ctxV') => OPE ctxV' ctxV -> Env ctx ctxV -> Env ctx ctxV'
strengthenEnv _   EmptyEnv         = EmptyEnv
strengthenEnv ope (ConsEnv tail v) = ConsEnv (strengthenEnv ope tail) (strengthenV ope v)

eval :: (SingContext ctxV) => Env ctx ctxV -> Expr ctx ty -> V ctxV ty
eval env (Var n) = envLookup n env
    where
        envLookup :: Elem ctx ty -> Env ctx ctxV -> V ctxV ty 
        envLookup Head     (ConsEnv _    v) = v
        envLookup (Tail n) (ConsEnv tail _) = envLookup n tail

eval (env :: Env ctx ctxV) (Lam (body :: Expr (arg:ctx) result)) = Function f 
    where
        f :: (SingContext ctxV') => OPE ctxV' ctxV -> V ctxV' arg -> V ctxV' result
        f ope v = eval (ConsEnv (strengthenEnv ope env) v) body

        -- NOTE: Typchecks without strengthening context if don't give f type declaration
        -- Uses scoped typed variables

eval env (App f n) = appV (eval env f) (eval env n) 
    where
        appV (Function f') n' = f' (idOPEFromEnv env) n'

        idOPEFromEnv :: (SingContext ctxV) => Env ctx ctxV -> OPE ctxV ctxV
        idOPEFromEnv _ = idOpe 

reify :: V ctx ty -> NormalForm ctx ty
reify (Base nf)    = nf
reify (Function f) = NormalLam (reify (f extendedOpe boundVar)) 
    where
        boundVar = etaExpand (NeutralVar Head)

        extendedOpe = extendOpe (Function f)

        extendOpe :: (SingContext ctx) => V ctx ty -> OPE (arg:ctx) ctx
        extendOpe _ = bindOpe 

normalise :: (SingContext ctx) => Expr ctx ty -> NormalForm ctx ty
normalise = reify . eval initialEnv

--- Normal form display

normaliseDB :: (SingContext ctx) => Expr ctx ty -> Untyped.DbExpr 
normaliseDB = normalToDB . normalise

normalToDB  :: NormalForm ctx ty -> Untyped.DbExpr 
normalToDB (NormalNeutral n) = neutralToDB n
normalToDB (NormalLam body)  = Untyped.DbLam (normalToDB body)

neutralToDB :: NeutralForm ctx ty -> Untyped.DbExpr 
neutralToDB (NeutralVar v)   = Untyped.DbVar (elemToIndex v)
neutralToDB (NeutralApp m n) = Untyped.DbApp (neutralToDB m) (normalToDB n)

elemToIndex :: Elem xs x -> Int
elemToIndex Head     = 0
elemToIndex (Tail n) = 1 + elemToIndex n

--- Singletons

class SingTy ty where
    etaExpand :: (SingContext ctx) => NeutralForm ctx ty -> V ctx ty

instance SingTy 'BaseTy where
    etaExpand n = Base (NormalNeutral n)

instance (SingTy arg, SingTy result) => SingTy (arg :-> result) where
    etaExpand (n :: NeutralForm ctx (arg :-> result)) = Function f 
        where
            f :: (SingContext ctx') => OPE ctx' ctx -> V ctx' arg -> V ctx' result
            f ope v = etaExpand (NeutralApp (strengthenNeutral ope n) (reify v)) 

class SingContext ctx where
    idOpe :: OPE ctx ctx
    bindOpe :: OPE (x:ctx) ctx
    bindOpe = Drop idOpe
    initialEnv :: Env ctx ctx

instance SingContext '[] where
    idOpe = Empty
    initialEnv = EmptyEnv

instance (SingContext xs, SingTy x) => SingContext (x:xs) where
    idOpe = Keep idOpe
    initialEnv = ConsEnv (strengthenEnv bindOpe initialEnv) (etaExpand (NeutralVar Head))
    
--- Combinators

identity :: (SingTy a) => Expr ctx (a :-> a)
identity = Lam (Var Head)

k :: (SingTy a, SingTy b) => Expr ctx (a :-> b :-> a)
k = Lam (Lam (Var (Tail Head)))

true :: Expr ctx ('BaseTy :-> 'BaseTy :-> 'BaseTy)
true = Lam (Lam (Var (Tail Head)))

false :: Expr ctx ('BaseTy :-> 'BaseTy :-> 'BaseTy)
false = Lam (Lam (Var Head))
