{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}
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
