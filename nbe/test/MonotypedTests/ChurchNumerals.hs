{-# LANGUAGE DataKinds, TypeOperators#-}
module MonotypedTests.ChurchNumerals (allTestsPassed) where

import Monotyped.NbE (
    Expr(..), 
    ClosedExpr, 
    Ty(..), 
    Elem(..), 
    normaliseDB,
    normalise,
    normalToDB
    )

type ChurchNumeralTy = ((BaseTy :-> BaseTy) :-> BaseTy :-> BaseTy)

type ChurchNumeral = ClosedExpr ChurchNumeralTy

app2 :: Expr ctx (a :-> b :-> c) -> Expr ctx a -> Expr ctx b -> Expr ctx c
app2 f x y = App (App f x) y 

toChurchNumeral :: Int -> ChurchNumeral
toChurchNumeral 0 = Lam (Lam (Var Head))
toChurchNumeral i = App churchSucc (toChurchNumeral (i - 1)) 
    where

        churchSucc :: ClosedExpr (ChurchNumeralTy :-> ChurchNumeralTy)
        churchSucc = Lam (Lam (Lam (App f (app2 n f x))))

        n = Var (Tail (Tail Head))
        f = Var (Tail Head)
        x = Var Head
    
addChurchNumeral :: ChurchNumeral -> ChurchNumeral -> ChurchNumeral
addChurchNumeral = app2 churchAdd
    where 
        churchAdd :: ClosedExpr (ChurchNumeralTy :-> ChurchNumeralTy :-> ChurchNumeralTy)
        churchAdd = Lam (Lam (Lam (Lam (app2 m f (app2 n f x)))))

        m = Var (Tail (Tail (Tail Head)))
        n = Var (Tail (Tail Head))
        f = Var (Tail Head)
        x = Var Head 

prop_add :: Int -> Int -> Bool 
prop_add m n = normaliseDB (addChurchNumeral (toChurchNumeral m) (toChurchNumeral n)) 
            == normaliseDB (toChurchNumeral (m + n))

multChurchNumeral :: ChurchNumeral -> ChurchNumeral -> ChurchNumeral
multChurchNumeral = app2 churchMult
    where 
        churchMult :: ClosedExpr (ChurchNumeralTy :-> ChurchNumeralTy :-> ChurchNumeralTy)
        churchMult = Lam (Lam (Lam (Lam (app2 m (App n f) x))))

        m = Var (Tail (Tail (Tail Head)))
        n = Var (Tail (Tail Head))
        f = Var (Tail Head)
        x = Var Head 

prop_mult :: Int -> Int -> Bool 
prop_mult m n = normaliseDB (multChurchNumeral (toChurchNumeral m) (toChurchNumeral n)) == normaliseDB (toChurchNumeral (m * n))

unitTests :: [Bool]
unitTests = [
    prop_mult 5 8,
    prop_mult 32 566,
    prop_add 3 5,
    prop_add 90 345,
    normaliseDB (multChurchNumeral (addChurchNumeral (toChurchNumeral 4) (toChurchNumeral 5)) (toChurchNumeral 3)) == normaliseDB (toChurchNumeral 27)
  ]

allTestsPassed :: Bool
allTestsPassed = and unitTests