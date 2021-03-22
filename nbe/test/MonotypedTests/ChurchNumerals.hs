{-# LANGUAGE DataKinds, TypeOperators, PolyKinds, GADTs #-}
module ChurchNumerals () where

import Monotyped.TypeDeclarations (
    Expr(..), 
    ClosedExpr, 
    Ty(..), 
    Elem(..), 
    normaliseDB
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
addChurchNumeral i j = App (App churchAdd i) j
    where 
        churchAdd :: ClosedExpr (ChurchNumeralTy :-> ChurchNumeralTy :-> ChurchNumeralTy)
        churchAdd = Lam (Lam (Lam (Lam (app2 m f (app2 n f x)))))

        m = Var (Tail (Tail (Tail Head)))
        n = Var (Tail (Tail Head))
        f = Var (Tail Head)
        x = Var Head 
{-

TODO:
- church multiplication
- church exponentiation
- church booleans
- testing 
    - quickcheck over values

-}