{-
Contributors: Liam O'Connor-Davis and Constantinos Paraskevopoulos
Last updated: September 2016
Description: Implements an evaluator for the Haskell subset MinHS.
-}

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
  | Param String
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
  _        -> error (show x) --"runtime error: undefined variable"

-- evaluates list constructors and primops
evalE g (Con "Nil") = Nil
evalE g (App (App (Con "Cons") (Num x)) xs) = Cons (x) (evalE g xs)
evalE g (App (Prim Null) (e)) = case (evalE g e) of
  Nil -> B True
  _   -> B False
evalE g (App (Prim Head) (e)) = case (evalE g e) of
  Nil         -> error "runtime error: empty list has no head"
  (Cons x xs) -> I x
evalE g (App (Prim Tail) (e)) = case (evalE g e) of
  Nil         -> error "runtime error: empty list has no tail"
  (Cons x xs) -> (Cons x xs)
--  (Cons x xs) -> let (Cons x' xs') = evalE g (App (Con "Cons") xs)
--                 in Cons x' xs'
-- TODO: tail not working fully

-- evaluates let bindings
evalE g (Let [Bind x (y) [] e1] e2) =
  let
    e1' = evalE g e1         -- evaluates the binding expression
    g'  = (E.add g (x, e1')) -- updates environment with new binding
  in evalE g' e2             -- evaluates the body of the binding

-- evaluates function applications
evalE g (App e1 e2) =
  let
    v1 = evalE g' e1
    v2 = evalE g e2
    g' = (E.add g ("x", v2))
---------
-- and do a case (E.lookup g v1) of ... to give the actual value of "x" above
-- but also need to store f = param when handling letfun!
--    param = case (E.lookup g v1) of
--      (Just v1') -> v1'
--      _          -> error "runtime error: undefined variable"    
---------
  in v1

--evalE g (App (Var f) e2) = case (E.lookup g f) of
--  (Just v) -> v --let
                --e2' = evalE g e2
                --g' = (E.add g (v, e2'))
              --in evalE g' v
--  _        -> error "runtime error: undefined function"

-- evaluates function values
-- TODO: types are ignored for now
evalE g (Letfun (Bind f (Arrow (TypeCon t1) (TypeCon t2)) [param] body)) =
  let
    g' = (E.add g (f, Param param))
  in evalE g body
--THIS ONE WORKS BUT WITHOUT HANDLING param: evalE g (Letfun (Bind f (Arrow (TypeCon t1) (TypeCon t2)) [param] body)) = evalE g body

-- terminates in error for all other expressions
evalE _ e = error (show e)

--convert :: Value -> Expr
--convert (Cons x) = (App (App (Cons x xs)))
-- TODO: implement an unevaluator for tail

-- evaluates comparison operators
evalCmp :: Integer -> Integer -> Op -> Bool
evalCmp a b Eq = a == b
evalCmp a b Ne = a /= b
evalCmp a b Gt = a  > b
evalCmp a b Lt = a  < b
evalCmp a b Ge = a >= b
evalCmp a b Le = a <= b
