
module UntypedTests.GensymNbE (gensymBenchmarks) where
import Criterion.Main
import Untyped.TypeDeclarations (Name, Expr(..)) 

import Untyped.GensymNbE ( normalise )

gensymBenchmarks :: Benchmark
gensymBenchmarks = bgroup "Gensym" [
    bench "1"  $ nf normalise (ExpApp k1 identity)               
  ]

--- Combinators

identity :: Expr
identity = ExpLam "x" (ExpVar "x")

k :: Expr
k = ExpLam "x" (ExpLam "y" (ExpVar "x"))

k1 :: Expr
k1 = ExpLam "x" (ExpLam "y" (ExpVar "y"))

omega :: Expr
omega = ExpApp (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x"))) (ExpLam "x" (ExpApp (ExpVar "x") (ExpVar "x")))