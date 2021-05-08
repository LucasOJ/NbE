module UntypedTests.DeBruijnNbE (allTestsPassed) where
import Untyped.TypeDeclarations (DbExpr(..))
import Untyped.DeBruijnNbE ( normalise, normaliseDbExpr )

app2 :: DbExpr -> DbExpr -> DbExpr -> DbExpr
app2 f x = DbApp (DbApp f x)

--- Church Numerals

toChurchNumeral :: Int -> DbExpr
toChurchNumeral 0 = DbLam (DbLam (DbVar 0))
toChurchNumeral i = DbApp churchSucc (toChurchNumeral (i - 1))
    where

        churchSucc :: DbExpr
        churchSucc = DbLam (DbLam (DbLam (DbApp f (app2 n f x))))

        n = DbVar 2
        f = DbVar 1
        x = DbVar 0

addChurchNumeral :: DbExpr -> DbExpr -> DbExpr
addChurchNumeral = app2 churchAdd
    where
        churchAdd :: DbExpr
        churchAdd = DbLam (DbLam (DbLam (DbLam (app2 m f (app2 n f x)))))

        m = DbVar 3
        n = DbVar 2
        f = DbVar 1
        x = DbVar 0

prop_add :: Int -> Int -> Bool
prop_add m n = normalise (addChurchNumeral (toChurchNumeral m) (toChurchNumeral n)) == normalise (toChurchNumeral (m + n))

multChurchNumeral :: DbExpr -> DbExpr -> DbExpr
multChurchNumeral = app2 churchMult
    where
        churchMult :: DbExpr
        churchMult = DbLam (DbLam (DbLam (DbLam (app2 m (DbApp n f) x))))

        m = DbVar 3
        n = DbVar 2
        f = DbVar 1
        x = DbVar 0

prop_mult :: Int -> Int -> Bool
prop_mult m n = normalise (multChurchNumeral (toChurchNumeral m) (toChurchNumeral n)) == normalise (toChurchNumeral (m * n))

--- Church Booleans

true :: DbExpr
true = k

false :: DbExpr
false = k1

churchIf :: DbExpr -> DbExpr -> DbExpr -> DbExpr
churchIf = app2

churchAnd :: DbExpr -> DbExpr -> DbExpr
churchAnd = app2 andExpr
    where
        andExpr :: DbExpr
        andExpr = DbLam (DbLam (app2 m n k1))

        m = DbVar 1
        n = DbVar 0

churchOr :: DbExpr  -> DbExpr -> DbExpr
churchOr = app2 orExpr
    where
        -- We need ChurchBoolTy (ChurchBoolTy a) since first argument is a HOF
        orExpr :: DbExpr
        orExpr = DbLam (DbLam (app2 m k n))

        m = DbVar 1
        n = DbVar 0

churchNot :: DbExpr -> DbExpr
churchNot = DbApp notExpr
    where
        notExpr :: DbExpr
        notExpr = DbLam (app2 (DbVar 0) k1 k)

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
    normalise (DbApp (DbLam (DbVar 1)) (DbVar 2)) == normalise (DbVar 0),
    normalise (DbApp identity (DbVar 0)) == normalise (DbVar 0),
    normalise (DbApp identity (DbVar 3)) == normalise (DbVar 3)
  ]

allTestsPassed :: Bool
allTestsPassed = and unitTests

--- Combinators

identity :: DbExpr
identity = DbLam (DbVar 0)

k :: DbExpr
k = DbLam (DbLam (DbVar 1))

k1 :: DbExpr
k1 = DbLam (DbLam (DbVar 0))
