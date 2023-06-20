

------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x)   = x
      f i (Lambda x m)   = if elem i [2,3] then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 1 m 
      f i (Apply  m n)   = if elem i   [3] then "(" ++ s ++ ")" else s where s = f 2 m ++ " " ++ f 3 n

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals


numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))


-- - - - - - - - - - - -- Renaming, substitution, beta-reduction


used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x m) = [x] `merge` used m
used (Apply  m n) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename y z (Variable x)
    | y == x    = Variable z
    | otherwise = Variable x
rename y z (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda x (rename y z m)
rename y z (Apply m n) = Apply (rename y z m) (rename y z n)

substitute :: Var -> Term -> Term -> Term
substitute y p (Variable x)
    | y == x    = p
    | otherwise = Variable x
substitute y p (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda z (substitute y p (rename x z m))
    where z = fresh (used p `merge` used m `merge` [x,y])
substitute y p (Apply m n) = Apply (substitute y p m) (substitute y p n)

beta :: Term -> [Term]
beta (Apply (Lambda x m) n) =
  [substitute x n m] ++ 
  [Apply (Lambda x m') n  | m' <- beta m] ++
  [Apply (Lambda x m ) n' | n' <- beta n]
beta (Variable _) = []
beta (Lambda x m) = [Lambda x m' | m' <- beta m]
beta (Apply  m n) =
  [Apply m' n  | m' <- beta m] ++
  [Apply m  n' | n' <- beta n]


-- - - - - - - - - - - -- Normalize


normalize :: Term -> IO ()
normalize m = do
  print m
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)


------------------------- Assignment 1: Combinators

--infixl 5 :@ 

data Combinator

{-
example1 :: Combinator
example1 = S :@ K :@ K :@ V "x"

example2 :: Combinator
example2 = S :@ (K :@ K) :@ I :@ V "x" :@ V "y"

-- - - - - - - - - - - -- show, parse

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
    down cs (' ':str) = down cs str
    down cs ('(':str) = down (Nothing : cs) str
    down cs ('I':str) = up cs I str
    down cs ('K':str) = up cs K str
    down cs ('S':str) = up cs S str
    down cs ( c :str) = up cs (V [c]) str
    up :: [Maybe Combinator] -> Combinator -> String -> Combinator
    up    []  c [] = c 
    up (Just c  : cs) d      str  = up cs (c:@d) str
    up (Nothing : cs) d (')':str) = up cs     d  str
    up            cs  d      str  = down (Just d : cs) str

-}

-- - - - - - - - - - - -- step, run

step :: Combinator -> [Combinator]
step = undefined


run :: Combinator -> IO ()
run = undefined


------------------------- Assignment 2: Combinators to Lambda-terms

toLambda :: Combinator -> Term
toLambda = undefined


------------------------- Assignment 3: Lambda-terms to Combinators

abstract :: Var -> Combinator -> Combinator
abstract = undefined

toCombinator :: Term -> Combinator
toCombinator = undefined

------------------------- Assignment 4: Estimating growth

sizeL :: Term -> Int
sizeL = undefined

sizeC :: Combinator -> Int
sizeC = undefined

series :: Int -> Term
series = undefined


------------------------- Assignment 5: Optimised interpretation

data Complexity = Linear | Quadratic | Cubic | Exponential

comb :: Term -> Combinator
comb = undefined

claim :: Complexity
claim = undefined
