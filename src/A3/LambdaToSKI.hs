module A3.LambdaToSKI where

import Data.Map (Map)
import Data.Set (Set)

import Data.Map qualified as Map
import Data.Set qualified as Set

-- IMPORTS --
-- import A3.SKI
-- import A3.LoopyLambda 

------------------------------------ SKI --------------------
-- SKI data type
data SKI = 
      S 
    | K 
    | I 
    | Apply SKI SKI 
    | Bracket SKI
  deriving Show 

ski :: SKI -> Maybe SKI

-- Values 
ski S = Nothing
ski K = Nothing
ski I = Nothing

-- Reduction Rules with no preconditions
ski (Apply I x) = Just x
ski (Apply (Apply K x) _) = Just x
ski (Apply (Apply (Apply S x) y) z) = Just (Apply (Apply x z) (Bracket (Apply y z)))

-- Reducing an Application 
-- first reduce the outer/left expression 'a' then, when 'a' is a normal form, evaluate 'b' 
ski (Apply a b) = 
  let reducedA = ski a in 
  case reducedA of 
    Nothing -> 
      let reducedB = ski b in 
      case reducedB of
        Nothing -> Nothing 
        Just v -> (Just (Apply a v)) 
    Just v -> (Just (Apply v b))

-- Bracket 
-- evaluate the inside first, then remove the brackets once 'a' is a normal form
ski (Bracket a) =
  let reducedA = ski a in 
    case reducedA of 
      Nothing -> Just a
      Just v -> Just (Bracket v)

-- Equality Instance ( used for assertEq in testing)
instance Eq (SKI) where
  (==) S S = True
  (==) K K = True
  (==) I I = True
  (==) (Apply w x) (Apply y z) = (w == y) && (x == z)
  (==) (Bracket x) (Bracket y) = x == y
  (==) _ _ = False



--------------------------------------- LAMBDA -----------------------------

-- | Syntax for the loopy lambda language.
data Expr
    = Var String
    -- ^ Variables: 'x'
    | Lam String Expr
    -- ^ Lambdas: 'λ x. e'
    | App Expr Expr
    -- ^ Application: 'e e'
    | Zero
    -- ^ Zero: '0'
    | PlusOne Expr
    -- ^ Successor: '1 + e'
    | Loop Expr Expr Expr
    -- ^ Loops: 'loop e e e'
    deriving (Show)

-- * Operations on variables

-- | Compute the set of free variables of an expression.
freeVars :: Expr -> Set String
freeVars (Var x) = Set.singleton x
freeVars (Lam x e) = Set.delete x (freeVars e)
freeVars (App e1 e2) = Set.union (freeVars e1) (freeVars e2)
freeVars Zero = Set.empty
freeVars (PlusOne e) = freeVars e
freeVars (Loop e1 e2 e3) = Set.unions [freeVars e1, freeVars e2, freeVars e3]

-- | Compute the set of all variables of an expression, free or bound.
allVars :: Expr -> Set String
allVars (Var x) = Set.singleton x
allVars (Lam x e) = Set.insert x (freeVars e)
allVars (App e1 e2) = Set.union (freeVars e1) (freeVars e2)
allVars Zero = Set.empty
allVars (PlusOne e) = allVars e
allVars (Loop e1 e2 e3) = Set.unions [allVars e1, allVars e2, allVars e3]

-- | Pick a name that isn't found in the provided set of names.
freshen :: String -> Set String -> String
freshen name avoid | Set.member name avoid = freshen (name ++ "'") avoid
                    | otherwise = name

-- | 'transpose x y a' will swap 'a' if it is 'x' or 'y', and leave it unchanged otherwise
transpose :: String -> String -> String -> String
transpose x y a | a == x = y
                | a == y = x
                | otherwise = a

-- | Swap the names 'x' and 'y' in an expression.
swapNames :: String -> String -> Expr -> Expr
swapNames x y (Var v) = Var (transpose x y v)
swapNames x y (Lam v e) = Lam (transpose x y v) (swapNames x y e)
swapNames x y (App e1 e2) = App (swapNames x y e1) (swapNames x y e2)
swapNames _ _ Zero = Zero
swapNames x y (PlusOne e) = PlusOne (swapNames x y e)
swapNames x y (Loop e1 e2 e3) = Loop (swapNames x y e1) (swapNames x y e2) (swapNames x y e3)

-- | Rename a term to not use the names in the provided list.
rename :: Expr -> Set String -> Expr                   
rename e avoid = go e Map.empty
    where
    -- Basic algorithm is to track what we have renamed variables
    -- to, and then freshen each bound variable.
    go :: Expr -> Map String String -> Expr
    go (Var x) rn =
        case Map.lookup x rn of
        Just y -> Var y
        Nothing -> Var x
    go (Lam x e) rn =
        -- Invent a new name for 'x', and then record
        -- it's new name.
        let x' = freshen x avoid in
        Lam x' (go e (Map.insert x x' rn))
    go (App e1 e2) rn =
        App (go e1 rn) (go e2 rn)
    go Zero _ =
        Zero
    go (PlusOne e) rn =
        PlusOne (go e rn)
    go (Loop n s f) rn =
        Loop (go n rn) (go s rn) (go f rn)
                    

-- * Comparing expressions for equality
alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v1) (Var v2) = v1 == v2
alphaEq (Lam v1 e1) (Lam v2 e2) =
    -- Pick a name that doesn't occur anywhere in 'e1' or 'e2',
    -- replace all occurances of 'v1' and 'v2' with this new name, then
    -- keep comparing for α-equivalence.
    let v' = freshen "x" (Set.unions [Set.fromList [v1, v2], allVars e1, allVars e2])
    in alphaEq (swapNames v' v1 e1) (swapNames v' v2 e2)
alphaEq (App f1 a1) (App f2 a2) =
    alphaEq f1 f2 && alphaEq a1 a2
alphaEq Zero Zero = True
alphaEq (PlusOne e1) (PlusOne e2) =
    alphaEq e1 e2
alphaEq (Loop n1 s1 f1) (Loop n2 s2 f2) = 
    alphaEq n1 n2 && alphaEq s1 s2 && alphaEq f1 f2
alphaEq _ _ = False

-- * Capture-avoiding substitution

-- | Substitute every occurance of 'e1' for 'x' in 'e2'.
subst :: String -> Expr -> Expr -> Expr
subst x e1 e2 = substRenamed x e1 (rename e2 (freeVars e1))
    where
    substRenamed :: String -> Expr -> Expr -> Expr
    substRenamed x _ (Var v) | v == x = e1
                            | otherwise = Var v
    substRenamed x e (Lam v body) | v == x = Lam v body
                                | otherwise = Lam v (substRenamed x e body)
    substRenamed x e (App f a) = App (substRenamed x e f) (substRenamed x e a)
    substRenamed _ _ Zero = Zero
    substRenamed x e (PlusOne n) = PlusOne (substRenamed x e n)
    substRenamed x e (Loop n s f) =
        Loop (substRenamed x e n) (substRenamed x e s) (substRenamed x e f)

-- * Question 2.1:

-- stepLoop will evaluate to Nothing if no steps are possible
stepLoop :: Expr -> Maybe Expr
--Normal Forms
stepLoop (Zero) = Nothing
stepLoop (Var _) = Nothing
stepLoop (Lam _ _) = Nothing 

--Lambda Application: (λx. e1) e2 -> e1[e2/x]
stepLoop (App (Lam x e1) e2) = Just (subst x e2 e1)

-- Application: e1 -> e1' / e1 e2 ->  e1' e2
stepLoop (App e1 e2) = 
    let v1 = stepLoop e1 in 
        case v1 of 
            Nothing -> Nothing 
            Just v -> Just (App v e2)

--PlusOne Rule: e -> e' / 1 + e -> 1 + e'
stepLoop (PlusOne e) = 
    let v1 = stepLoop e in 
        case v1 of 
            Nothing -> Nothing 
            Just v -> Just (PlusOne v)

-- Loops 
-- loop 0 e2 e3 -> e2
stepLoop (Loop Zero e2 _) = Just e2

-- loop (1 + e1) e2 e3 -> e3 (loop e1 e2 e3)
stepLoop (Loop (PlusOne e1) e2 e3) = Just (App e3 (Loop e1 e2 e3))

-- e1 -> e1' / loop e1 e2 e3 -> loop e1' e2 e3
stepLoop (Loop e1 e2 e3) = 
    let v1 = stepLoop e1 in 
        case v1 of 
            Nothing -> Nothing 
            Just v -> Just (Loop v e2 e3)


-- Eq instance for Expr (used in testing)
-- since stepLoop returns type 'Maybe Expr', the provided function could not be used directly
instance Eq (Expr) where
    (==) a b = alphaEq a b

-- END OF IMPORTS --



------------------------------------------------------------------------------
-- BONUS 2 -------------------------------------------------------------------
------------------------------------------------------------------------------

-- Explanation 
{- 
    Firstly, I have created an "in between" calculus in order to 
    translate lambda calculus to SKI. This is the data type LambdaToSKI. 

    In addition, to translate the constructors Zero, (PlusOne e), and Loop, I 
    first translate these constructors into pure lambda calculus, and 
    then translate that to SKI. 

    Resources Used: 
        -- https://blog.ngzhian.com/ski2.html
        -- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis
        -- https://www.cs.tufts.edu/comp/105-2020f/handouts/lambda-coding.pdf
        -- https://www.youtube.com/watch?v=qzsxO79zxS8
        -- https://risingentropy.com/for-loops-and-bounded-quantifiers-in-lambda-calculus/ 
        -- https://en.wikipedia.org/wiki/Lambda_calculus --pred function
-}

-- the in between calculus
data LambdaToSKI = 
      Var2 String 
    | App2 LambdaToSKI LambdaToSKI
    | Lam2 String LambdaToSKI
    | S2
    | K2
    | I2
    | T LambdaToSKI LambdaToSKI
    deriving Show 
    
-- returns the set of all free variables in the given expression
-- pretty much identical to the provided function freeVars
freeVars2 :: LambdaToSKI -> Set String
freeVars2 (Var2 x) = Set.singleton x
freeVars2 (Lam2 x e) = Set.delete x (freeVars2 e)
freeVars2 (App2 e1 e2) = Set.union (freeVars2 e1) (freeVars2 e2)
freeVars2 (T e1 e2) = Set.union (freeVars2 e1) (freeVars2 e2)
freeVars2 _ = Set.empty

-- Translates a Lambda expression to the in between calculus
-- For the pure lambda calculus constructors, this is simply a 
-- change in syntax: 
--      Var x -> Var2 x
--      Lam x e -> Lam2 x e
--      App e1 e2 -> App2 e1 e2
-- For Zero, PlusOne, and Loop, they are translated into pure
-- lambda calculus and then, from there, switched to the in 
-- between calculus

lambdaToInbetween :: Expr -> LambdaToSKI
lambdaToInbetween (Var x) = Var2 x
lambdaToInbetween (Lam x e) = Lam2 x (lambdaToInbetween e)
lambdaToInbetween (App e1 e2) = App2 (lambdaToInbetween e1) (lambdaToInbetween e2) 

-- Zero -> Lam f. Lam x. x
lambdaToInbetween (Zero) = lambdaToInbetween (Lam "f" (Lam "x" (Var "x")))
-- PlusOne (Zero) -> Lam f. Lam x. f x
lambdaToInbetween (PlusOne Zero) = lambdaToInbetween (Lam "f" (Lam "x" (App (Var "f") (Var "x"))))
-- PlusOne e -> (Lam n. Lam f. Lam x. nfx) e
-- the succ function
lambdaToInbetween (PlusOne e) = lambdaToInbetween (App (Lam "n" (Lam "f" (Lam "x" (App (Var "f") (App (App (Var "n") (Var "f")) (Var "x")))))) e)

-- the loop can be translated into the following recursive if statement: 
-- if (e1 isZero) then e2
-- else if (e1 is PlusOne e) then e3 (loop e e2 e3)
-- else loop e1 e2 e3
-- this can be translated into lambda calculus 

lambdaToInbetween (Loop e1 e2 e3) = lambdaToInbetween (App (App (App (Lam "loop" (Lam "e1" (Lam "e2" (Lam "e3" (
        App
            (App 
                (App ift (App (Lam "n" (App (App (Var "n") (App t f)) (t))) (Var "e1")) ) --check if e1 is zero
            (Var "e2"))  --if true, return e2
        (App --if e1 is not zero
            (App 
                (App ift (App isSucc (Var "e1"))) --check if e1 is a successor 
                    (App (App (App (Var "loop") (App predL (Var "e1"))) (Var "e2")) (Var "e3"))) -- if it is, return with the pred
        (App (App (App (Var "loop") (Var "e1")) (Var "e2")) (Var "e3"))) -- if not, keep the same (we could reduce e1 but that is not in the translation)
    ))))) e1) e2) e3)

-- true in lambda calculus
t :: Expr 
t = (Lam "a" (Lam "b" (Var "a"))) 

-- false in lambda calculus
f :: Expr
f =  (Lam "a" (Lam "b" (Var "b"))) --same as zero 

-- an if statement in lambda calculus
-- if m then t else f
ift :: Expr
ift = Lam "m" (Lam "t" ( Lam "f" (App (App (Var "m") (Var "t")) (Var "f"))))

-- get the predecessor 
predL :: Expr 
predL = Lam "n" (Lam "f" (Lam "x" (App 
        ( App 
            (App (Var "n") (Lam "g" (Lam "h" (App (Var "h") (App (Var "g") (Var "f"))))) 
            ) (Lam "u" (Var "x"))
        ) (Lam "u" (Var "u"))
    )))

-- returns t if input n is a successor
isSucc :: Expr 
isSucc = Lam "n" (App f (App (Var "n") (App f (App t t))))

-- now we take the translate lambda -> in between version 
-- and reduce it to only the SKI elements of our in between calculus 
-- rules from: https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis 
-- inspiration for the implementation from: https://blog.ngzhian.com/ski2.html
toInBetween :: LambdaToSKI -> Maybe LambdaToSKI 
toInBetween (Var2 x) = Just (Var2 x)
toInBetween S2 = Just S2
toInBetween K2 = Just K2
toInBetween I2 = Just I2
toInBetween (T e1 e2) = Just (T e1 e2)

toInBetween (App2 e1 e2) = 
    case toInBetween e1 of 
        Nothing -> Nothing
        Just v1 -> 
            case toInBetween e2 of 
                Nothing -> Nothing 
                Just v2 -> Just (App2 v1 v2)

toInBetween (Lam2 x e1) = 
    if (not (Set.member x (freeVars2 e1))) then 
        case toInBetween e1 of 
            Just v1 -> Just (App2 K2 v1)
            Nothing -> Nothing 
    else 
        case e1 of 
            Var2 y -> if x == y then Just (I2) else Nothing
            Lam2 y e2 -> 
                if (Set.member x (freeVars2 e2)) 
                then case toInBetween (Lam2 y e2) of 
                    Just v -> toInBetween (Lam2 x v)
                    Nothing -> Nothing 
                else Nothing
            App2 e2 e3 -> 
                if ((Set.member x (freeVars2 e2)) || (Set.member x (freeVars2 e3)))
                    then 
                        case toInBetween (Lam2 x e2) of 
                            Nothing -> Nothing 
                            Just v2 -> 
                                case toInBetween (Lam2 x e3) of 
                                    Nothing -> Nothing 
                                    Just v3 -> Just (App2 (App2 S2 v2) v3)
                    else Nothing
            otherwise -> Nothing -- ??

-- now we take this SKI version of the in between calculus, 
-- and if we can, we translate it to SKI 
-- this returns Nothing if the translation is not possible
inBetweenToSKI :: LambdaToSKI -> Maybe SKI
inBetweenToSKI (Var2 _) = Nothing
inBetweenToSKI (Lam2 _ _) = Nothing
inBetweenToSKI S2 = Just S
inBetweenToSKI K2 = Just K
inBetweenToSKI I2 = Just I 
inBetweenToSKI (App2 e1 e2) =
    case inBetweenToSKI e1 of 
        Nothing -> Nothing
        Just v1 -> 
            case inBetweenToSKI e2 of 
                Nothing -> Nothing
                Just v2 -> Just (Apply v1 v2)
inBetweenToSKI (T e1 e2) =  -- ????
    case inBetweenToSKI e1 of 
        Nothing -> Nothing
        Just v1 -> 
            case inBetweenToSKI e2 of 
                Nothing -> Nothing
                Just v2 -> Just (Apply v1 v2)


-- putting it all together 
translate :: Expr -> Maybe SKI 
translate e = 
    let v = toInBetween (lambdaToInbetween e) in 
        case v of 
            Just v' -> inBetweenToSKI v'
            Nothing -> Nothing