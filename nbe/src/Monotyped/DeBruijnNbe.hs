{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
module Monotyped.DeBruijnNbE () where

import Monotyped.TypeDeclarations

-- ty should remain the same always
eval' :: Env ctx -> Expr ctx ty -> V ctx ty
eval' env (Var elemProof) = envLookup elemProof env 
eval' env (Lam body) = Function f where
    f v = eval' env' body where
        env' = Shift v env
eval' env (App m n) = app (eval' env m) (eval' env n) 

evalFunction :: Env (arg : ctx) -> Expr (arg : ctx) ty -> V ctx ty
evalFunction env body = undefined 

-- the parameters of this type definition are fixed by NeutralVApp
app :: V ctx (Arrow arg result) -> V ctx arg -> V ctx result 
app (Function f) v = f v
app (Up m) n = Up (NeutralVApp m n) 

reify :: Int -> V ctx t -> NormalExpr ctx t
reify k (Function f) = NormalLam (reify (k + 1) (f (Up (NeutralVVar Head))))
reify k (Up m) = NormalNeutral (reifyNeutral k m)

reifyNeutral :: Int -> NeutralV ctx t -> NeutralExpr ctx t
-- wrong!! elemProof realtive to global term - need something "local"
reifyNeutral k (NeutralVVar elemProof) = NeutralVar elemProof 

reifyNeutral k (NeutralVApp m n) = NeutralApp (reifyNeutral k m) (reify k n)

--- Debug
eval :: Expr '[] t -> V ctx t
eval = undefined 

isNormal :: NormalExpr '[] t -> Bool 
isNormal _ = True

exprToString :: Expr '[] t -> String
exprToString = exprToString'

exprToString' :: Expr ctx t -> String
exprToString' (Var _) = "Var"
exprToString' (Lam body) = "Lam ( " ++ exprToString' body ++ " )"
exprToString' (App m n) = "App " ++ exprToString' m ++ " " ++ exprToString' n

-- TODO: How to represent environment and tie in with type environent in type?

elemToIndex :: Elem xs s -> Int
elemToIndex Head = 0
elemToIndex (Tail n) = 1 + elemToIndex n

--- Combinators

identity :: Expr ctx (Arrow a a)
identity = Lam (Var Head)

k1 :: Expr ctx (Arrow a (Arrow b a))
k1 = Lam (Lam (Var (Tail Head)))

k2 :: Expr ctx (Arrow a (Arrow b b))
k2 = Lam (Lam (Var Head))

--exprToString' :: Expr a t -> String