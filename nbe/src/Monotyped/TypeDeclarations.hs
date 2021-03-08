
{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs, RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
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

 -- order preserving embeddings
data OPE :: [Ty] -> [Ty] -> * where
    Empty :: OPE '[] '[]
    Drop  :: OPE ctx1 ctx2 -> OPE (x : ctx1) ctx2
    Keep  :: OPE ctx1 ctx2 -> OPE (x : ctx1) (x : ctx2)

-- Q: type family for id_e? How to represent function on types?

weakenElem :: OPE weak strong -> Elem strong ty -> Elem weak ty
weakenElem Empty      v        = v
weakenElem (Drop ope) v        = Tail (weakenElem ope v)
weakenElem (Keep ope) Head     = Head
weakenElem (Keep ope) (Tail v) = Tail (weakenElem ope v)

-- weakenExpr :: OPE weak strong -> Expr strong ty -> Expr weak ty
-- weakenExpr ope (Var n) = Var (weakenElem ope n)
-- weakenExpr ope (Lam body) = Lam (weakenExpr (Keep ope) body)
-- weakenExpr ope (App f a) = App (weakenExpr ope f) (weakenExpr ope a)

weakenNormal :: OPE weak strong -> NormalExpr strong ty -> NormalExpr weak ty
weakenNormal ope (NormalNeutral n) = NormalNeutral (weakenNeutral ope n)
weakenNormal ope (NormalLam n) = NormalLam (weakenNormal (Keep ope) n)

weakenNeutral :: OPE weak strong -> NeutralExpr strong ty -> NeutralExpr weak ty
weakenNeutral ope (NeutralVar n) = NeutralVar (weakenElem ope n)
weakenNeutral ope (NeutralApp f a) = NeutralApp (weakenNeutral ope f) (weakenNormal ope a) 

composeOPEs :: OPE b c -> OPE a b -> OPE a c
composeOPEs v        Empty    = v
composeOPEs v        (Drop u) = Drop (composeOPEs v u)
composeOPEs (Drop v) (Keep u) = Drop (composeOPEs v u)
composeOPEs (Keep v) (Keep u) = Keep (composeOPEs v u)

data V :: [Ty] -> Ty -> * where 
    Up :: NormalExpr ctx BaseTy -> V ctx BaseTy
    Function :: (OPE weak strong -> V weak arg -> V weak result) -> V strong (Arrow arg result)
    
weakenV :: OPE weak strong -> V strong ty -> V weak ty
weakenV ope (Up nf) = Up (weakenNormal ope nf)
weakenV ope (Function f) = Function f' where
    f' ope' = f (composeOPEs ope ope')

data Env :: [Ty] -> [Ty] -> * where
    EmptyEnv :: Env '[] ctxV
    ConsEnv  :: Env ctx ctxV -> V ctxV ty -> Env (ty : ctx) ctxV
    -- Q: What's the point of ctxV? Context to return into?
    -- Q: Why only contains Vs with same semantic context?

envLookup :: Elem ctx ty -> Env ctx ctxV -> V ctxV ty 
envLookup Head     (ConsEnv _ v)    = v
envLookup (Tail n) (ConsEnv prev _) = envLookup n prev

weakenEnv :: OPE c b -> Env a b -> Env a c
weakenEnv _ EmptyEnv = EmptyEnv
weakenEnv ope (ConsEnv tail v) = ConsEnv (weakenEnv ope tail) (weakenV ope v)

eval :: Expr ctx ty -> Env ctx ctxV -> V ctxV ty
eval (Var n)    env = envLookup n env
eval (Lam body) env = Function f where 
    f ope v = eval body (ConsEnv (weakenEnv ope env) v)
    -- Q: 
eval (App f a)  env = appV (eval f env) (eval a env) where
    appV :: V ctxV (Arrow arg ty) -> V ctxV arg -> V ctxV ty
    appV (Function f) a' = undefined 
    -- TODO: fix this!

-- appV :: Env ctx ctxV -> V ctxV (Arrow arg ty) -> V ctxV arg -> V ctxV ty
-- appV env (Function f) = f idOPE 
{-
idOPE :: forall (tys :: [Ty]). OPE tys tys
idOPE = undefined 

type family IdOPE (ctxV :: [Ty]) :: OPE ctxV ctxV where
    IdOPE '[]      = Empty
    IdOPE (x : xs) = Keep (IdOPE xs)
-}
data STy :: Ty -> * where
    SBaseTy :: STy BaseTy
    SArrow  :: (SingTy a, SingTy b) => STy a -> STy b -> STy (Arrow a b)

class SingTy a where
    singTy :: STy a 

instance SingTy 'BaseTy where
    singTy = SBaseTy

instance (SingTy a, SingTy b) => SingTy ('Arrow a b) where
    singTy = SArrow singTy singTy

data SList :: [Ty] -> * where
    SEmpty :: SList '[]
    SCons  :: STy a -> SList xs -> SList xs

class SingCon xs where
    idOpe :: OPE xs xs

instance SingCon '[] where
    idOpe = Empty

instance (SingCon xs) => SingCon (x:xs) where
    idOpe = Keep idOpe

opeFromEnv :: Env ctx ctxV -> OPE ctx ctx
opeFromEnv EmptyEnv = Empty
opeFromEnv (ConsEnv env v) = Keep (opeFromEnv env)

reify :: V ctx ty -> NormalExpr ctx ty
reify (Up nf)      = nf
--reify (Function f) = NormalLam (reify ())

evalNeutral :: (SingTy ty) => NeutralExpr ctx ty -> V ctx ty
evalNeutral = evalNeutral' singTy

evalNeutral' :: STy ty -> NeutralExpr ctx ty -> V ctx ty
evalNeutral' SBaseTy       n = Up (NormalNeutral n)  
evalNeutral' (SArrow a b)  n = Function f where
    -- TODO: Type properly (relies on Any)
    --f :: OPE ctx1 ctx2 -> V ctx2 arg -> V ctx1 result
    f ope v = evalNeutral (NeutralApp (weakenNeutral ope n) (reify v))

normalise :: Expr '[] ty -> NormalExpr '[] ty
normalise t = reify (eval t EmptyEnv)
