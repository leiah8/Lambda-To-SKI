module A3.SKI where

-- * Question 1: Revenge of the Goblins and Gnomes

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

  