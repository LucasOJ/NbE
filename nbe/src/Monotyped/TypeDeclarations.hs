
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

emplist :: [a]
emplist = []

 -- order preserving embeddings
data OPE :: [Ty] -> [Ty] -> * where
    Empty :: OPE emplist emplist
    Drop  :: OPE ctx1 ctx2 -> OPE (x : ctx1) ctx2
    Keep  :: OPE ctx1 ctx2 -> OPE (x : ctx1) (x : ctx2)

-- Q: type family for id_e? How to represent function on types?

weakenElem :: OPE weak strong -> Elem strong ty -> Elem weak ty
weakenElem Empty v = v
weakenElem (Drop ope) v = Tail (weakenElem ope v)
weakenElem (Keep ope) Head = Head
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
composeOPEs v Empty = v
composeOPEs v (Drop u) = Drop (composeOPEs v u)
composeOPEs (Drop v) (Keep u) = Drop (composeOPEs v u)
composeOPEs (Keep v) (Keep u) = Keep (composeOPEs v u)

data V :: [Ty] -> Ty -> * where 
    Up :: NormalExpr ctx BaseTy -> V ctx BaseTy
    --Function ::  OPE weak strong -> (V weak arg -> V weak result) -> V strong (Arrow arg result)
    -- Q: Feels like this is going the wrong way (possible to strengthen context? Subsitution?)
    Function :: OPE weak strong -> (V weak arg -> V weak result) -> V weak (Arrow arg result)
    -- Q: In https://github.com/dpndnt/library/blob/master/doc/pdf/kovacs-2017.pdf this is a function not a datatype
    -- Q: How to pattern match on it?

weakenV :: OPE weak strong -> V strong ty -> V weak ty
weakenV ope (Up nf) = Up (weakenNormal ope nf)
weakenV ope (Function ope' f) = Function ope'' f where
    ope'' = composeOPEs ope' ope

data Env :: [Ty] -> [Ty] -> * where
    EmptyEnv :: Env '[] ctx
    ConsEnv  :: Env ctx ctxV -> V ctxV ty -> Env (ty : ctx) ctxV
    -- Q: What's the point of ctxV? Context to return into?

envLookup :: Elem ctx ty -> Env ctx ctxV -> V ctxV ty 
envLookup Head     (ConsEnv _ v)    = v
envLookup (Tail n) (ConsEnv prev _) = envLookup n prev

weakenEnv :: OPE b c -> Env a b -> Env a c
weakenEnv _ EmptyEnv = EmptyEnv
weakenEnv ope (ConsEnv tail v) = ConsEnv (weakenEnv ope tail) (weakenV ope v)

eval :: Expr ctx ty -> Env ctx ctxV -> V ctxV ty
eval (Var n)    env = envLookup n env
eval (Lam body) env = Function ope f where 
    f v = eval body (ConsEnv env v)
-- Q: Why does the lambda in the paper have 2 args? 
eval (App f a)  env = appV (eval f env) (eval a env) 

appV :: V ctx (Arrow arg ty) -> V ctx arg -> V ctx ty
appV (Function ope f) a = f a 


-- data NeutralV :: Ty -> * where 
--     -- Need to be element of context?
--     NeutralVVar :: Elem ctx ty -> NeutralV ty
--     NeutralVApp :: NeutralV (Arrow arg result) -> V arg -> NeutralV result 
{-
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
-}

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