------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x : xs) (y : ys)
  | x == y = x : merge xs ys
  | x <= y = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x : xs) (y : ys)
  | x < y = x : minus xs (y : ys)
  | x == y = minus xs ys
  | otherwise = minus (x : xs) ys

variables :: [Var]
variables = [[x] | x <- ['a' .. 'z']] ++ [x : show i | i <- [1 ..], x <- ['a' .. 'z']]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [x | x <- xs, not (elem x ys)]

fresh :: [Var] -> Var
fresh = head . removeAll variables

-- - - - - - - - - - - -- Terms

type Var = String

data Term
  = Variable Var
  | Lambda Var Term
  | Apply Term Term

pretty :: Term -> String
pretty = f 0
  where
    f i (Variable x) = x
    f i (Lambda x m) = if elem i [2, 3] then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 1 m
    f i (Apply m n) = if elem i [3] then "(" ++ s ++ ")" else s where s = f 2 m ++ " " ++ f 3 n

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals

numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0 = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i - 1))

-- - - - - - - - - - - -- Renaming, substitution, beta-reduction

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x m) = [x] `merge` used m
used (Apply m n) = used n `merge` used m

rename :: Var -> Var -> Term -> Term
rename y z (Variable x)
  | y == x = Variable z
  | otherwise = Variable x
rename y z (Lambda x m)
  | y == x = Lambda x m
  | otherwise = Lambda x (rename y z m)
rename y z (Apply m n) = Apply (rename y z m) (rename y z n)

substitute :: Var -> Term -> Term -> Term
substitute y p (Variable x)
  | y == x = p
  | otherwise = Variable x
substitute y p (Lambda x m)
  | y == x = Lambda x m
  | otherwise = Lambda z (substitute y p (rename x z m))
  where
    z = fresh (used p `merge` used m `merge` [x, y])
substitute y p (Apply m n) = Apply (substitute y p m) (substitute y p n)

beta :: Term -> [Term]
beta (Apply (Lambda x m) n) =
  [substitute x n m]
    ++ [Apply (Lambda x m') n | m' <- beta m]
    ++ [Apply (Lambda x m) n' | n' <- beta n]
beta (Variable _) = []
beta (Lambda x m) = [Lambda x m' | m' <- beta m]
beta (Apply m n) =
  [Apply m' n | m' <- beta m]
    ++ [Apply m n' | n' <- beta n]

-- - - - - - - - - - - -- Normalize

normalize :: Term -> IO ()
normalize m = do
  print m
  let ms = beta m
  if null ms
    then return ()
    else normalize (head ms)

------------------------- Assignment 1: Combinators

infixl 5 :@

data Combinator
  = I
  | K
  | S
  | V String
  | Combinator :@ Combinator
  deriving (Eq)

example1 :: Combinator
example1 = S :@ K :@ K :@ V "x"

example2 :: Combinator
example2 = S :@ (K :@ K) :@ I :@ V "x" :@ V "y"

instance Show Combinator where
  show = f 0
    where
      f _ I = "I"
      f _ K = "K"
      f _ S = "S"
      f _ (V s) = s
      f i (c :@ d) = if i == 1 then "(" ++ s ++ ")" else s where s = f 0 c ++ " " ++ f 1 d

parse :: String -> Combinator
parse s = down [] s
  where
    down :: [Maybe Combinator] -> String -> Combinator
    down [Just c] [] = c
    down [] [] = error "Empty input string"
    down cs [] = error "Invalid input string or unmatched parentheses"
    down cs (' ' : str) = down cs str
    down cs ('(' : str) = down (Nothing : cs) str
    down cs ('I' : str) = up cs I str
    down cs ('K' : str) = up cs K str
    down cs ('S' : str) = up cs S str
    down cs (c : str) = up cs (V [c]) str
    up :: [Maybe Combinator] -> Combinator -> String -> Combinator
    up [] c [] = c
    up (Just c : cs) d str = up cs (c :@ d) str
    up (Nothing : cs) d (')' : str) = up cs d str
    up cs d str = down (Just d : cs) str

-- - - - - - - - - - - -- step, run

step :: Combinator -> [Combinator]
step (I :@ x) = x : [I :@ x' | x' <- step x]
step (K :@ x :@ y) = [x] ++ [K :@ x' :@ y | x' <- step x] ++ [K :@ x :@ y' | y' <- step y]
step (S :@ x :@ y :@ z) = [x :@ z :@ (y :@ z)] ++ [S :@ x' :@ y :@ z | x' <- step x] ++ [S :@ x :@ y' :@ z | y' <- step y] ++ [S :@ x :@ y :@ z' | z' <- step z]
step I = []
step K = []
step S = []
step (V _) = []
step (c1 :@ c2) = [c1' :@ c2 | c1' <- step c1] ++ [c1 :@ c2' | c2' <- step c2]


run :: Combinator -> IO ()
run c = do
  print c
  let nextSteps = step c
  if null nextSteps
    then return ()
    else run (head nextSteps)


------------------------- Assignment 2: Combinators to Lambda-terms

toLambda :: Combinator -> Term
toLambda I = Lambda "x" (Variable "x")
toLambda K = Lambda "x" (Lambda "y" (Variable "x"))
toLambda S = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x") (Variable "z")) (Apply (Variable "y") (Variable "z")))))
toLambda (V x) = Variable x
toLambda (c1 :@ c2) = Apply (toLambda c1) (toLambda c2)

------------------------- Assignment 3: Lambda-terms to Combinators


abstract :: Var -> Combinator -> Combinator
abstract x (V y)
  | x == y = I
  | otherwise = K :@ V y
abstract x I = K :@ I
abstract x K = K :@ K
abstract x S = K :@ S
abstract x (c1 :@ c2) = S :@ abstract x c1 :@ abstract x c2


toCombinator :: Term -> Combinator
toCombinator (Variable x) = V x
toCombinator (Lambda x t) = abstract x (toCombinator t)
toCombinator (Apply t1 t2) = toCombinator t1 :@ toCombinator t2

------------------------- Assignment 4: Estimating growth

sizeL :: Term -> Int
sizeL (Variable _) = 1
sizeL (Lambda _ t) = 1 + sizeL t
sizeL (Apply t1 t2) = 1 + sizeL t1 + sizeL t2


sizeC :: Combinator -> Int
sizeC (V _) = 1
sizeC I = 1
sizeC K = 1
sizeC S = 1
sizeC (c1 :@ c2) = 1 + sizeC c1 + sizeC c2


series :: Int -> Term
series 0 = Lambda "a" (Variable "a")
series n = foldr (\_ acc -> Lambda "f" acc) (Lambda "x" (iterate (Apply (Variable "f")) (Variable "x") !! n)) [1 .. n]



------------------------- Assignment 5: Optimised interpretation

data Complexity = Linear | Quadratic | Cubic | Exponential

comb :: Term -> Combinator
comb = undefined

claim :: Complexity
claim = undefined
