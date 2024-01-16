-- |
module LoopyLambdaTests (lambdaTests) where
import A3.LoopyLambda

import Test.HUnit

-- | Helper for testing α-equivalence of expressions.
-- IS NOT USED 
-- assertAlphaEqual :: String -> Expr -> Expr -> Assertion
-- assertAlphaEqual msg e1 e2 = assertBool msg (alphaEq e1 e2)


-- NOTE: The format of test cases is as follows: 
-- t0 = TestCase (assertEqual "description" 
--     ("Expecteed Value")
--     ("Expression"))

-- 28 total tests 
lambdaTests :: Test
lambdaTests = TestList [ t1, t2, t3, t4, t5, t6, t7, t8, 
    t9, t10, t11, t11A, t12, t12A, t13, t13A, t14, t14A, t15, t16, 
    t17, t18, t19, t20, t21, t22, t23, t24 ]


-- Values
t1 :: Test 
t1 = TestCase (assertEqual "Zero" 
    (Nothing)
    (stepLoop (Zero)) )

t2 :: Test 
t2 = TestCase (assertEqual "x" 
    (Nothing)
    (stepLoop (Var "x")) )

-- Lambda Cases

-- Normal Form
t3 :: Test 
t3 = TestCase (assertEqual "Lam x. y" 
    (Nothing)
    (stepLoop (Lam "x" (Var "y"))) )

-- Applying Lambda 
t4 :: Test 
t4 = TestCase (assertEqual "(Lam x. y) z" 
    (Just (Var "y"))
    (stepLoop (App (Lam "x" (Var "y")) (Var "z"))) )

t5 :: Test 
t5 = TestCase (assertEqual "(Lam y . xy) z" 
    (Just (App (Var "x") (Var "z")))
    (stepLoop (App (Lam "y" (App (Var "x") (Var "y"))) (Var "z"))) )

-- Identity 
t6 :: Test 
t6 = TestCase (assertEqual "(Lam x . x) z" 
    (Just (Var "z"))
    (stepLoop (App (Lam "x" (Var "x")) (Var "z"))) )


-- Application 

-- Normal Forms
t7 :: Test 
t7 = TestCase (assertEqual "xy" 
    (Nothing) 
    (stepLoop (App (Var "x") (Var "y"))) )

t8 :: Test 
t8 = TestCase (assertEqual "Zero y" 
    (Nothing) 
    (stepLoop (App (Zero) (Var "y"))) )

-- Nested Normal Form
-- e1 cannot be reduced, so the expression cannot be reduced
t9 :: Test 
t9 = TestCase (assertEqual "y (Lam x. x) z" 
    (Nothing) 
    (stepLoop (App (Var "y") (App (Lam "x" (Var "x")) (Var "z")))) )

-- e1 -> e1' / e1 e2 -> e1' e2
t10 :: Test 
t10 = TestCase (assertEqual "((Lam x.x) z) y" 
    (Just (App (Var "z") (Var "y"))) 
    (stepLoop (App (App (Lam "x" (Var "x")) (Var "z")) (Var "y"))) )


-- PlusOne Reduction Rules 

-- Normal Form
t11 :: Test 
t11 = TestCase (assertEqual "1 + 0" 
    (Nothing) 
    (stepLoop (PlusOne Zero)) )

-- Nested Normal Form
t11A :: Test 
t11A = TestCase (assertEqual "1 + 1 + 1 + 0" 
    (Nothing) 
    (stepLoop (PlusOne (PlusOne (PlusOne Zero)))) )

-- e -> e' / 1 + e -> 1 + e'
t12 :: Test 
t12 = TestCase (assertEqual "1 + ((Lam x. x) 0)" 
    (Just (PlusOne Zero)) 
    (stepLoop (PlusOne (App (Lam "x" (Var "x")) (Zero)))) )

t12A :: Test 
t12A = TestCase (assertEqual "1 + (loop 0 0 0)" 
    (Just (PlusOne Zero)) 
    (stepLoop (PlusOne (Loop (Zero) (Zero) (Zero)))) )

-- Loops Reduction Rules 

-- e1 -> e1' / loop e1 e2 e3 -> loop e1' e2 e3
t13 :: Test 
t13 = TestCase (assertEqual "loop ((Lam x.x ) 0) x y" 
    (Just (Loop (Zero) (Var "x") (Var "y"))) 
    (stepLoop (Loop (App (Lam "x" (Var "x")) (Zero)) (Var "x") (Var "y"))) )

-- nested loops
t13A :: Test
t13A = TestCase (assertEqual "loop ((loop 0 z z) 0) x y" 
    (Just (Loop (Var "z") (Var "x") (Var "y"))) 
    (stepLoop (Loop (Loop (Zero) (Var "z") (Var "z")) (Var "x") (Var "y"))) )

-- loop (1 + e1) e2 e3 -> e3 (loop e1 e2 e3)
t14 :: Test 
t14 = TestCase (assertEqual "loop (1 + 0) x y" 
    (Just (App (Var "y") (Loop Zero (Var "x") (Var "y")))) 
    (stepLoop (Loop (PlusOne Zero) (Var "x") (Var "y"))) )

t14A :: Test 
t14A = TestCase (assertEqual "loop (1 + ((Lam.x.x) 0)) x y" 
    (Just (App (Var "y") (Loop (App (Lam "x" (Var "x")) (Zero)) (Var "x") (Var "y")))) 
    (stepLoop (Loop (PlusOne (App (Lam "x" (Var "x")) (Zero))) (Var "x") (Var "y"))) )

-- loop 0 e2 e3 -> e2
t15 :: Test 
t15 = TestCase (assertEqual "loop 0 x y" 
    (Just (Var "x")) 
    (stepLoop (Loop Zero (Var "x") (Var "y"))) )

t16 :: Test 
t16 = TestCase (assertEqual "loop ((Lam x.x) 0) x y" 
    (Just (Loop (Zero) (Var "x") (Var "y"))) 
    (stepLoop (Loop (App (Lam "x" (Var "x")) (Zero)) (Var "x") (Var "y"))) )


-- Normal Form (e1 cannot be reduced)
t17 :: Test 
t17 = TestCase (assertEqual "y (loop (((Lam x.x) 0) x y)" 
    (Nothing) 
    (stepLoop (App (Var "y") (Loop (App (Lam "x" (Var "x")) (Zero)) (Var "x") (Var "y")))) )


-- Construct Student Number (Strings)
-- Base Case
baseCase :: Expr
baseCase = (App (App (App (App (App (App (App (App (Var "4") (Var "0")) (Var "0")) (Var "3")) (Var "6")) (Var "2")) (Var "1")) (Var "6")) (Var "6"))

t18 :: Test 
t18 = TestCase (assertEqual "Base Case: 400362166" 
    (Nothing) 
    (stepLoop (baseCase))) 

-- Using a Loop 
t19Inner :: Expr
t19Inner = (App (App (App (App (App (App (App (Var "4") (Var "0")) (Var "0")) (Var "3")) (Var "6")) (Var "2")) (Var "1")) (Var "6"))

t19 :: Test
t19 = TestCase (assertEqual "(loop 0 4003621 0) 6" 
    (Just (baseCase)) 
    (stepLoop (App (Loop (Zero) (t19Inner) (Var "0")) (Var "6") )) )

-- Applying a Lambda
-- replace 0 with 0
t20 :: Test
t20 = TestCase (assertEqual "(Lam 0. 400362166) 0" 
    (Just (baseCase)) 
    (stepLoop (App (Lam ("0") (baseCase) ) (Var "0"))) )

-- replace 6 with b
baseCase2 :: Expr
baseCase2 = (App (App (App (App (App (App (App (App (Var "4") (Var "0")) (Var "0")) (Var "3")) (Var "b")) (Var "2")) (Var "1")) (Var "b")) (Var "b"))
    
t21 :: Test
t21 = TestCase (assertEqual "(Lam b. 4003b21bb) 6" 
    (Just (baseCase)) 
    (stepLoop (App (Lam ("b") (baseCase2) ) (Var "6"))) )


-- tN :: Test 
-- tN = TestCase (assertEqual "" () (stepLoop ()) )

-- Construct Student Number (Natural Numbers)
baseCaseNum :: Expr
baseCaseNum = makeNum 66 Zero

makeNum :: Integer -> Expr -> Expr
makeNum 0 e = e
makeNum n e = makeNum (n-1) (PlusOne e)

t22 :: Test 
t22 = TestCase (assertEqual "loop 0 (66 as a number) 0" 
    (Just (baseCaseNum)) 
    (stepLoop (Loop Zero baseCaseNum Zero)) )

t23 :: Test 
t23 = TestCase (assertEqual "1 + ((Lam x. x) (65 as a number))" 
    (Just (baseCaseNum)) 
    (stepLoop (PlusOne (App (Lam "x" (Var "x")) (makeNum 65 Zero)))) )

t24 :: Test
t24 = TestCase (assertEqual "(Lam x. (1 + x)) (65 as a number)" 
    (Just (baseCaseNum)) 
    (stepLoop (App (Lam "x" (PlusOne (Var "x"))) (makeNum 65 Zero))) )
