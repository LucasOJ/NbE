
module UntypedTests.GensymNbE (gensymBenchmarks, allTestsPassed) where
import Criterion.Main
import Untyped.TypeDeclarations (Name, Expr(..))
import Data.Set
import Untyped.GensymNbE ( normalise, normaliseToExpr )
import Untyped.Utils ( getFreshVariableStream )

gensymBenchmarks :: Benchmark
gensymBenchmarks = bgroup "Gensym" [
    bench "1"  $ nf normalise (ExpApp k1 identity)
  ]

app2 :: Expr -> Expr -> Expr -> Expr
app2 f x = ExpApp (ExpApp f x)

--- Church Numerals

toChurchNumeral :: Int -> Expr
toChurchNumeral = toChurchNumeral' ["v" ++ show i | i <- [0..]]

toChurchNumeral' :: [Name] -> Int -> Expr
toChurchNumeral' (v0:v1:vs)    0 = ExpLam v0 (ExpLam v1 (ExpVar v1))
toChurchNumeral' (n':f':x':vs) i = ExpApp churchSucc (toChurchNumeral' vs (i - 1))
    where

        churchSucc :: Expr
        churchSucc = ExpLam n' (ExpLam f' (ExpLam x' (ExpApp f (app2 n f x))))

        n = ExpVar n'
        f = ExpVar f'
        x = ExpVar x'

addChurchNumeral :: Expr -> Expr -> Expr
addChurchNumeral m n  = app2 churchAdd m n
    where
        churchAdd :: Expr
        churchAdd = ExpLam v0' (ExpLam v1' (ExpLam f' (ExpLam x' (app2 v0 f (app2 v1 f x)))))

        v0' = head freeVariables
        v1' = freeVariables!!1
        f'  = freeVariables!!2
        x'  = freeVariables!!3

        v0 = ExpVar v0'
        v1 = ExpVar v1'
        f  = ExpVar f'
        x  = ExpVar x'

        boundVariables = getBoundVariables n `union` getBoundVariables m
        freeVariables = getFreshVariableStream boundVariables

getBoundVariables :: Expr -> Set Name
getBoundVariables (ExpVar _)      = empty
getBoundVariables (ExpLam v body) = insert v $ getBoundVariables body
getBoundVariables (ExpApp m n)    = getBoundVariables m `union` getBoundVariables n

prop_add :: Int -> Int -> Bool
prop_add m n = normalise (addChurchNumeral (toChurchNumeral m) (toChurchNumeral n)) == normalise (toChurchNumeral (m + n))

multChurchNumeral :: Expr -> Expr -> Expr
multChurchNumeral m n = app2 churchMult m n
    where
        churchMult :: Expr
        churchMult = ExpLam v0' (ExpLam v1' (ExpLam f' (ExpLam x' (app2 v0 (ExpApp v1 f) x))))

        v0' = head freeVariables
        v1' = freeVariables!!1
        f'  = freeVariables!!2
        x'  = freeVariables!!3

        v0 = ExpVar v0'
        v1 = ExpVar v1'
        f  = ExpVar f'
        x  = ExpVar x'

        boundVariables = getBoundVariables n `union` getBoundVariables m
        freeVariables = getFreshVariableStream boundVariables

prop_mult :: Int -> Int -> Bool
prop_mult m n = normalise (multChurchNumeral (toChurchNumeral m) (toChurchNumeral n)) == normalise (toChurchNumeral (m * n))

--- Church Booleans

true :: Expr
true = k

false :: Expr
false = k1

churchIf :: Expr -> Expr -> Expr -> Expr
churchIf = app2

churchAnd :: Expr -> Expr -> Expr
churchAnd m n = app2 andExpr m n
    where
        andExpr :: Expr
        andExpr = ExpLam v0' (ExpLam v1' (app2 v0 v1 k1))

        v0' = head freeVariables
        v1' = freeVariables!!1

        v0 = ExpVar v0'
        v1 = ExpVar v1'

        boundVariables = getBoundVariables n `union` getBoundVariables m `union` getBoundVariables true
        freeVariables = getFreshVariableStream boundVariables

churchOr :: Expr -> Expr -> Expr
churchOr m n = app2 orExpr m n
    where
        -- We need ChurchBoolTy (ChurchBoolTy a) since first argument is a HOF
        orExpr :: Expr
        orExpr = ExpLam v0' (ExpLam v1' (app2 v0 k v1))

        v0' = head freeVariables
        v1' = freeVariables!!1

        v0 = ExpVar v0'
        v1 = ExpVar v1'

        boundVariables = getBoundVariables n `union` getBoundVariables m `union` getBoundVariables false
        freeVariables = getFreshVariableStream boundVariables

churchNot :: Expr -> Expr
churchNot n = ExpApp notExpr n
    where
        notExpr :: Expr
        notExpr = ExpLam v0' (app2 v0 k1 k)

        v0' = head freeVariables
        v0  = ExpVar v0'

        boundVariables = getBoundVariables n `union` getBoundVariables false `union` getBoundVariables true
        freeVariables = getFreshVariableStream boundVariables

--- Unit tests

unitTests :: [Bool]
unitTests = [
    prop_mult 5 8,
    prop_mult 32 566,
    prop_add 3 5,
    prop_add 90 345,
    normalise (multChurchNumeral (addChurchNumeral (toChurchNumeral 4) (toChurchNumeral 5)) (toChurchNumeral 3)) == normalise (toChurchNumeral 27),
    normalise (churchNot true) == normalise false,
    normalise (churchNot false) == normalise true,
    normalise (churchAnd (churchNot true) (churchOr false true)) == normalise false,
    normalise (churchAnd (churchNot false) (churchOr false true)) == normalise true,
    normalise (churchAnd (churchAnd true true) (churchOr false true)) == normalise true,
    normalise (churchAnd (churchAnd true true) (churchOr false false)) == normalise false,
    normalise (ExpApp (ExpLam "x" (ExpVar "y")) (ExpVar "z")) == normalise (ExpVar "y"),
    normalise (ExpApp identity (ExpVar "z")) == normalise (ExpVar "z")
  ]

allTestsPassed :: Bool
allTestsPassed = and unitTests

--- Combinators

identity :: Expr
identity = ExpLam "x" (ExpVar "x")

k :: Expr
k = ExpLam "x" (ExpLam "y" (ExpVar "x"))

k1 :: Expr
k1 = ExpLam "x" (ExpLam "y" (ExpVar "y"))

omega :: Expr
omega = ExpApp (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x"))) (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x")))