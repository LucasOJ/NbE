{-# LANGUAGE GADTs, DataKinds, PolyKinds, TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
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

deriving instance (Eq (Elem xs x))

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

data OPE :: [Ty] -> [Ty] -> * where
    Empty :: OPE '[] '[]
    Drop  :: OPE ctx1 ctx2 -> OPE (x : ctx1) ctx2
    Keep  :: OPE ctx1 ctx2 -> OPE (x : ctx1) (x : ctx2) 

instance Show (OPE a b) where
    show Empty = "Empty"
    show (Drop n) = "Drop " ++ show n
    show (Keep n) = "Keep " ++ show n

-- CODE BELOW IS HYPOTHETICAL

data Expr' = Var' Ty [Ty] Int
           | Lam' Ty [Ty] Expr'
           | App' Ty [Ty] Expr' Expr'

data V :: [Ty] -> Ty -> * where 
    Base :: NormalForm ctx BaseTy -> V ctx BaseTy
    Function :: (V (x:ctx) arg -> V (x:ctx) result) -> V ctx (arg :-> result)

data Env :: [Ty] -> [Ty] -> * where
    EmptyEnv :: Env '[] ctxV
    ConsEnv  :: Env ctx ctxV -> V ctxV ty -> Env (ty : ctx) ctxV


class SingContext ctx where
    idOpe :: OPE ctx ctx

instance SingContext '[] where
    idOpe = Empty

instance (SingContext xs) => SingContext (x:xs) where
    idOpe = Keep idOpe

data Exp a where
    I   :: Int  -> Exp Int
    B   :: Bool -> Exp Bool
    Add :: Exp Int -> Exp Int -> Exp Int
    Mul :: Exp Int -> Exp Int -> Exp Int
    Eq  :: Eq a => Exp a -> Exp a -> Exp Bool

deriving instance (Show (Exp a))

-- instance Eq (NormalForm ctx ty) where
--     (NormalNeutral n) == (NormalNeutral m) = n == m
--     (NormalLam n) == (NormalLam m) = n == m
--     _ == _ = False
-- 
-- instance Eq (NeutralForm ctx ty) where
--     (NeutralVar n) == (NeutralVar m) = n == m
--     (==) (NeutralApp (n :: NeutralForm ctx (arg1 :-> ty)) m) 
--          (NeutralApp (x :: NeutralForm ctx (arg2 :-> ty)) y) 
--           = n == x && m == y 
--     _ == _ = False