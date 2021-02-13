module TypeDeclarations ( 
    Expr(ExpVar, ExpLam, ExpApp), 
    DbExpr(DbVar, DbLam, DbApp), 
    Name 
) where

-- Syntax
type Name = String

-- String-named expressions
data Expr = ExpVar Name
          | ExpLam Name Expr
          | ExpApp Expr Expr
    deriving (Read, Show)

-- deBruijn index expressions
data DbExpr = DbVar Int
            | DbLam DbExpr
            | DbApp DbExpr DbExpr
    deriving (Read, Show)