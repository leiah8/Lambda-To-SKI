-- | Tests for question 1
module SKITests (skiTests) where

import A3.SKI
import Test.HUnit

-- NOTE: The format of test cases is as follows: 
-- t0 = TestCase (assertEqual "description" 
--     ("Expecteed Value")
--     ("Expression"))

skiTests :: Test
skiTests = TestList [t1, t2, t3, t4, t5, t6, t7, t7A, t8, t9, 
    t10, t11, t12, t13, t14, t15, t16, t17, t18]

-- Values: S, K, I
t1 :: Test 
t1 = TestCase (assertEqual "ski (S)" 
    (Nothing)
    (ski (S)) )


t2 :: Test 
t2 = TestCase (assertEqual "K" 
    (Nothing)
    (ski (K)) )


t3 :: Test 
t3 = TestCase (assertEqual "I" 
    (Nothing)
    (ski (I)) )

-- Normal Form: S K
t4 :: Test 
t4 = TestCase (assertEqual "S K" 
    (Nothing)
    (ski (Apply S K)) )

-- Bracket
t5 :: Test 
t5 = TestCase (assertEqual "(I)" 
    (Just I)
    (ski (Bracket I)) )

-- Evalueate I: Ix -> x
t6 :: Test 
t6 = TestCase (assertEqual "I S" 
    (Just S)
    (ski (Apply I S)) )

-- Normal Form: S K I
t7 :: Test 
t7 = TestCase (assertEqual "SKI" 
    (Nothing)
    (ski (Apply (Apply S K) I)) )

--Normal Form: S (K I)
t7A :: Test 
t7A = TestCase (assertEqual "S(KI)" 
    (Nothing)
    (ski (Apply S (Apply K I))) )

-- Left Associated: e1 -> e1' / e1 e2 -> e1' e2
t8 :: Test 
t8 = TestCase (assertEqual "IKS" 
    (Just (Apply K S))
    (ski (Apply (Apply I K) S)) )

t9 :: Test 
t9 = TestCase (assertEqual "(IK)(IS)" 
    (Just (Apply K (Apply I S)))
    (ski (Apply (Apply I K) (Apply I S))) )

-- Second Reduction Rule: e2 -> e2' / v1 e2 -> v1 e2'
t10 :: Test 
t10 = TestCase (assertEqual "I(IS)" 
    (Just (Apply I S))
    (ski (Apply I (Apply I S))) )


-- Evaluate K
t11 :: Test 
t11 = TestCase (assertEqual "KSI" 
    (Just S)
    (ski (Apply (Apply K S) I)) )

-- Evaluate S
t12 :: Test 
t12 = TestCase (assertEqual "SIIK" 
    (Just (Apply (Apply I K) (Bracket (Apply I K))))
    (ski (Apply (Apply (Apply S I) I) K)) )

--More Complex Reductions
t13 :: Test 
t13 = TestCase (assertEqual "(IK)(IK)" 
    (Just (Apply K (Bracket (Apply I K))))
    (ski (Apply (Apply I K) (Bracket (Apply I K)))) )

--Brackets Reduce First
t14 :: Test 
t14 = TestCase (assertEqual "K(IK)" 
    (Just (Apply K (Bracket K)))
    (ski (Apply K (Bracket (Apply I K)))) )

--Inner Bracket
t15 :: Test 
t15 = TestCase (assertEqual "K(K)" 
    (Just (Apply K K))
    (ski (Apply K (Bracket K))) )

-- Test Order of Operations 
--CHECK CORRECT: TO DO
t16 :: Test 
t16 = TestCase (assertEqual "S(II)" 
    (Just (Apply S I))
    (ski (Apply S (Apply I I))) )

t17 :: Test 
t17 = TestCase (assertEqual "SII" 
    (Nothing)
    (ski (Apply (Apply S I) I)) )

-- Complex Application of S
t18 :: Test 
t18 = TestCase (assertEqual "SKI(KIS)" 
    (Just (Apply (Apply K (Bracket (Apply (Apply K I) S))) (Bracket (Apply I (Bracket (Apply (Apply K I) S))))))
    (ski (Apply (Apply (Apply S K) I) (Bracket (Apply (Apply K I) S)))) )