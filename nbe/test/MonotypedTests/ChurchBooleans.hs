{-# LANGUAGE DataKinds, TypeOperators#-}
module MonotypedTests.ChurchBooleans () where

import Monotyped.NbE (
    Expr(..), 
    ClosedExpr, 
    Ty(..), 
    Elem(..), 
    normaliseDB,
    SingTy
    )

type ChurchBoolTy a = a :-> a :-> a

type ChurchBool a = ClosedExpr (ChurchBoolTy a)

type BaseChurchBool = ChurchBool BaseTy

app2 :: Expr ctx (a :-> b :-> c) -> Expr ctx a -> Expr ctx b -> Expr ctx c
app2 f x y = App (App f x) y 

-- Needs to be polymorphic
true :: (SingTy a) => ChurchBool a
true = Lam (Lam (Var (Tail Head)))  

false :: (SingTy a) => ChurchBool a
false = Lam (Lam (Var Head))

k :: (SingTy a) => Expr ctx (a :-> a :-> a)
k = Lam (Lam (Var (Tail Head))) 

k1 :: (SingTy a) => Expr ctx (a :-> a :-> a)
k1 =  Lam (Lam (Var Head))

{-
- Each church[Operation] function converts Haskell application into syntactic application
- Each [operation]Expr is the term operating on the church encoding
    -- Type signatures identical (Haskell application <-> syntactic Expr application) 
-}

-- First argument takes in HOF
churchIf :: (SingTy a) => ChurchBool (ChurchBoolTy a) -> ChurchBool a -> ChurchBool a -> ChurchBool a
churchIf = app2

prop_if_1 :: Bool
prop_if_1 = normaliseDB (churchIf true true false :: BaseChurchBool) == normaliseDB (true :: BaseChurchBool)

churchAnd :: (SingTy a) => ChurchBool (ChurchBoolTy a) -> ChurchBool a -> ChurchBool a
churchAnd = app2 andExpr
    where
        andExpr :: (SingTy a) => ClosedExpr (ChurchBoolTy (ChurchBoolTy a) :-> ChurchBoolTy a :-> ChurchBoolTy a)
        andExpr = Lam (Lam (app2 p q k1))

        p = Var (Tail Head)
        q = Var Head

churchOr :: (SingTy a) => ChurchBool (ChurchBoolTy a) -> ChurchBool a -> ChurchBool a
churchOr = app2 orExpr
    where
        -- We need ChurchBoolTy (ChurchBoolTy a) since first argument is a HOF
        orExpr :: (SingTy a) => ClosedExpr (ChurchBoolTy (ChurchBoolTy a) :-> ChurchBoolTy a :-> ChurchBoolTy a)
        orExpr = Lam (Lam (app2 p k q))

        p = Var (Tail Head)
        q = Var Head

churchNot :: (SingTy a) => ChurchBool (ChurchBoolTy a) -> ChurchBool a
churchNot = App notExpr
    where 
        notExpr :: (SingTy a) => ClosedExpr (ChurchBoolTy (ChurchBoolTy a) :-> ChurchBoolTy a)
        notExpr = Lam (app2 x k1 k) 

        x = Var Head