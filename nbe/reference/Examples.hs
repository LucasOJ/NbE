{-# LANGUAGE GADTs, DataKinds, PolyKinds, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Examples where

data Nat = Zero | Succ Nat

data Vec' :: Nat -> * where
    ZeroVec' :: Vec' 'Zero
    SuccVec' :: a -> Vec' n -> Vec' ('Succ n)


data Vec :: * -> Nat -> * where
    ZeroVec :: Vec a 'Zero
    SuccVec :: a -> Vec a n -> Vec a ('Succ n)

head' :: Vec a (Succ n) -> a
head' (SuccVec x xs) = x
-- head' (ZeroVec) = undefined 

data Ty = BaseTy | Ty :-> Ty 
    deriving (Show)
infixr 9 :->

data Elem :: [a] -> a -> * where
    -- Can construct such a proof if the value is at the beginning of the list
    Head :: Elem (x ': xs) x
    -- The proof is still valid is we prepend an element to the list
    Tail :: Elem xs x -> Elem (y ': xs) x

data Expr :: [Ty] -> Ty -> * where
    Var :: Elem ctx ty -> Expr ctx ty
    Lam :: Expr (arg ': ctx) result -> Expr ctx (arg ':-> result)
    App :: Expr ctx (arg ':-> result) -> Expr ctx arg -> Expr ctx result 

data NormalForm :: [Ty] -> Ty -> * where
    NormalNeutral :: NeutralForm ctx ty -> NormalForm ctx ty
    NormalLam     :: NormalForm (arg ': ctx) result -> NormalForm ctx (arg :-> result)    

data NeutralForm :: [Ty] -> Ty -> * where
    NeutralVar :: Elem ctx ty -> NeutralForm ctx ty
    NeutralApp :: NeutralForm ctx (arg :-> result) -> NormalForm ctx arg -> NeutralForm ctx result

-- CODE BELOW IS HYPOTHETICAL

data Expr' = Var' Ty [Ty] Int
           | Lam' Ty [Ty] Expr'
           | App' Ty [Ty] Expr' Expr'

data V :: [Ty] -> Ty -> * where 
    Base :: NormalForm ctx BaseTy -> V ctx BaseTy
    Function :: (V ctx arg -> V ctx result) -> V ctx (arg :-> result)

data Env :: [Ty] -> [Ty] -> * where
    EmptyEnv :: Env '[] ctxV
    ConsEnv  :: Env ctx ctxV -> V ctxV ty -> Env (ty : ctx) ctxV

eval :: Env ctx ctx -> Expr ctx ty -> V ctx ty
eval (env :: Env ctx ctxV) (Lam (body :: Expr (arg:ctx) result)) = Function f 
    where
        f :: V ctx arg -> V ctx result
        f v = eval (ConsEnv env v) body
