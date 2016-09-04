{-#
Contributors: Liam O'Connor-Davis and Constantinos Paraskevopoulos
Last updated: September 2016
Description: Implements an evaluator for the Haskell subset MinHS.
#-}

module MinHS.Evaluator where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type VEnv = E.Env Value

-- defines the values a program can be evaluated to
data Value
  = I Integer
  | B Bool
  | Nil
  | Cons Integer Value
  deriving (Show)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)
  pretty _ = undefined

-- evaluates a program to a value by calling
-- evalE with an empty environment
evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE E.empty e
evaluate bs = evalE E.empty (Let bs (Var "main"))

-- main evaluator function
-- assumes type checking succeeded
-- handles runtime errors like undefined variables and division by zero
evalE :: VEnv -> Exp -> Value

-- evaluates constants and booleans
evalE g (Num n)       = I n
evalE g (Con "True")  = B True
evalE g (Con "False") = B False

-- evaluates addition
evalE g (App (App (Prim Add) a) b) = case (evalE g a, evalE g b) of
  (I a', I b') -> I (a' + b')
  _            -> undefined

-- evaluates subtraction
evalE g (App (App (Prim Sub) a) b) = case (evalE g a, evalE g b) of
  (I a', I b') -> I (a' - b')
  _            -> undefined

-- evaluates multiplication
evalE g (App (App (Prim Mul) a) b) = case (evalE g a, evalE g b) of
  (I a', I b') -> I (a' * b')
  _            -> undefined

-- evaluates division
evalE g (App (App (Prim Quot) a) b) = case (evalE g a, evalE g b) of
  (I a',  I 0) -> error "runtime error: cannot divide by zero"
  (I a', I b') -> I (a' `div` b')
  _            -> undefined

-- evaluates modulus operator
evalE g (App (App (Prim Rem) a) b) = case (evalE g a, evalE g b) of
  (I a',  I 0) -> error "runtime error: cannot divide by zero"
  (I a', I b') -> I (a' `mod` b')
  _            -> undefined

-- evaluates negation operator
evalE g (App (Prim Neg) e) = case (evalE g e) of
  (I e) -> I (-e)
  _     -> undefined

-- evaluates comparison operators
evalE g (App (App (Prim op) a) b) = case (evalE g a, evalE g b) of
  (I a', I b') -> B (evalCmp a' b' op)
  _            -> undefined

-- evaluates if statements
evalE g (If e1 e2 e3) = case (evalE g e1) of
  B True  -> evalE g e2 -- evaluates 'then' branch
  B False -> evalE g e3 -- evaluates 'else' branch
  _       -> undefined

-- evaluates variables
evalE g (Var x) = case (E.lookup g x) of
  (Just v) -> v
  _        -> error "runtime error: undefined variable"

-- evaluates list constructors and primops
-- TODO
-- evalE g (Con Nill) = []

-- evaluates let bindings
evalE g (Let [Bind x (TypeCon y) [] e1] e2) =
  let
    e1' = evalE g e1        -- evaluates the binding expression
    g' = (E.add g (x, e1')) -- updates environment with new binding
  in evalE g' e2            -- evaluates the body of the binding

-- evaluates functions
-- TODO

-- terminates in error for all other expressions
evalE _ e = error (show e)

-- evaluates comparison operators
evalCmp :: Integer -> Integer -> Op -> Bool
evalCmp a b Eq = a == b
evalCmp a b Ne = a /= b
evalCmp a b Gt = a  > b
evalCmp a b Lt = a  < b
evalCmp a b Ge = a >= b
evalCmp a b Le = a <= b
