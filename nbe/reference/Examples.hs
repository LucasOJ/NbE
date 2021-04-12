{-# LANGUAGE GADTs, DataKinds, PolyKinds, TypeOperators #-}
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

data Expr' = Var' Ty [Ty] Int
           | Lam' Ty [Ty] Expr'
           | App' Ty [Ty] Expr' Expr'
