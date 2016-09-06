{-
Contributors: Liam O'Connor-Davis and Constantinos Paraskevopoulos
Last Updated: September 2016
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
  = I Integer                      -- integer value
  | B Bool                         -- boolean value
  | Nil                            -- empty list constructor
  | Cons Integer Value             -- list constructor
  | Closure VEnv String String Exp -- function closure
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
--  _        -> error (show x) -- TODO: check this

-- evaluates list constructors
evalE g (Con "Nil") = Nil
evalE g (App (App (Con "Cons") x) xs) = case (evalE g x) of
  (I n) -> (Cons (n) (evalE g xs))
  _     -> error "runtime error: type checking must have failed"

-- evaluates empty list inspector
evalE g (App (Prim Null) e) = case (evalE g e) of
  Nil -> B True
  _   -> B False

-- evaluates head
evalE g (App (Prim Head) e) = case (evalE g e) of
  (Cons x xs) -> I x
  Nil         -> error "runtime error: list is empty"
--  _ -> evalE g (App (Prim Head) (convert (evalE g e))) -- TODO: check this

-- evaluates tail
evalE g (App (Prim Tail) (App (App (Con "Cons") _) xs)) = evalE g xs
evalE g (App (Prim Tail) (Con "Nil")) = error "runtime error: list is empty"
evalE g (App (Prim Tail) x) = evalE g (App (Prim Tail) (convert (evalE g x)))

-- evaluates let bindings
-- type information is ignored
evalE g (Let [Bind x (_) [] e1] e2) =
  let
    e1' = evalE g e1         -- evaluates the binding expression
    g'  = (E.add g (x, e1')) -- updates environment with new binding
  in evalE g' e2             -- evaluates the body of the binding

-- evaluates function applications
evalE g (App e1 e2) =
  let
    v1@(Closure g' f x body) = evalE g e1
    v2   = evalE g e2          -- evaluates function argument
    g''  = (E.add g' (f, v1))  -- binds function name in body
    g''' = (E.add g'' (x, v2)) -- binds function parameter in body
  in evalE g''' body           -- evaluates function body

-- evaluates function values
-- type information is ignored
evalE g (Letfun (Bind f (_) [] body)) =
  let
    g' = (E.add g (f, f))--(evalE g f)))
  in evalE g' body -- TODO: check this
evalE g (Letfun (Bind f (_) [param] body)) = Closure g f param body

-- terminates in error for all other expressions
evalE _ e = error (show e)

-- converts evaluated expressions into abstract syntax expressions
-- used only to recover list constructors
convert :: Value -> Exp
convert Nil         = Con "Nil"
convert (Cons x xs) = (App (App (Con "Cons") (Num x)) (convert xs))

-- evaluates comparison operators
evalCmp :: Integer -> Integer -> Op -> Bool
evalCmp a b Eq = a == b
evalCmp a b Ne = a /= b
evalCmp a b Gt = a  > b
evalCmp a b Lt = a  < b
evalCmp a b Ge = a >= b
evalCmp a b Le = a <= b
