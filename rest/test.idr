--import Data.Vect

-- main : IO ()
-- main = do
-- 	putStrLn "test"
--
-- data Test = One | Two
--
-- data Test2 : Type where
--     One2 : Integer -> Test2
--     Two2 : Test2
--
-- AdderType : Nat -> Type -> Type
-- AdderType Z a = a
-- AdderType (S k) a = a -> AdderType k a
--
-- adder : (n:Nat) -> (acc: Int) -> AdderType n Int
-- adder Z acc = acc
-- adder (S k) acc = \x => adder k $ acc + x
--
-- data Format
--   = Number Format
--   | Str Format
--   | Lit String Format
--   | End
--
-- PrintfType : Format -> Type
-- PrintfType (Number fmt) = Int -> PrintfType fmt
-- PrintfType (Str fmt) = String -> PrintfType fmt
-- PrintfType (Lit s fmt) = PrintfType fmt
-- PrintfType End = String
--
-- printfFmt : (acc: String) -> (fmt: Format) -> PrintfType fmt
-- printfFmt acc (Number fmt) = \i => printfFmt (show i ++ acc) fmt
-- printfFmt acc (Str fmt) = \s => printfFmt (s ++ acc) fmt
-- printfFmt acc (Lit s fmt) = printfFmt (s ++ acc) fmt
-- printfFmt acc End = acc
--
-- toFormat : (xs: List Char) -> Format
-- toFormat [] = End
-- toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
-- toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
-- toFormat ('%' :: '%' :: chars) = Lit "%" (toFormat chars)
-- toFormat (x :: chars) = Lit (cast x) (toFormat chars)
--
-- printf : (str: String) -> PrintfType (toFormat (unpack str))
-- printf str = printfFmt "" $ toFormat $ unpack str
--
-- sumEntries' : Num a => (l: Nat) -> Vect n a -> Vect n a -> Maybe a
-- sumEntries' _ [] [] = Nothing
-- sumEntries' Z (x::_) (y::_) = Just $ x + y
-- sumEntries' (S k) (_::xs) (_::ys) = sumEntries' k xs ys
--
-- sumEntries : Num a => (i: Integer) -> Vect n a -> Vect n a -> Maybe a
-- sumEntries x = sumEntries' (cast x)
--
-- data Tree elem
--   = Empty
--   | Node (Tree elem) elem (Tree elem)
--
-- insert : Ord a => a -> Tree a -> Tree a
-- insert x Empty = Node Empty x Empty
-- insert x (Node l v r) = if (v < x) then Node l v (insert x r) else Node (insert x l) v r
--
-- listToTree : Ord a => List a -> Tree a
-- listToTree [] = Empty
-- listToTree (x::xs) = insert x $ listToTree xs
--
--
-- data Expr a
--   = Val a
--   | Add (Expr a) (Expr a)
--   | Sub (Expr a) (Expr a)
--   | Mul (Expr a) (Expr a)
--   | Abs (Expr a)
--
--
-- eval : (Neg a, Num a) => Expr a -> a
-- eval (Val i) = i
-- eval (Add x y) = eval x + eval y
-- eval (Sub x y) = eval x - eval y
-- eval (Mul x y) = eval x * eval y
-- eval (Abs x) = abs $ eval x
--
--
-- implementation Num a => Num (Expr a) where
--   (+) a b = Add a b
--   (*) a b = Mul a b
--   fromInteger n = Val $ fromInteger n
--
-- implementation (Num a, Neg a) => Neg (Expr a) where
--   (-) a b = Sub a b
--   abs a = Abs a
--   negate a = Sub (Val 0) a
--
-- implementation Functor Expr where
--   map f (Val a) = Val $ f a
--   map f (Add x y) = Add (map f x) (map f y)
--   map f (Sub x y) = Sub (map f x) (map f y)
--   map f (Mul x y) = Mul (map f x) (map f y)
--   map f (Abs x) = Abs (map f x)


data Tree' : Int -> Type where
 Empty' : Tree' 0
 Node' : Tree' x -> (v: Int) -> Tree' y -> Tree' (x + v + y)

treeSum : Tree' n -> Int
treeSum {n} _ = n

insertType : (x: Int) -> Tree' n -> Int
insertType x Empty' = 0 + x + 0
insertType x (Node' l v r) =
	if (v < x) then treeSum l + v + (insertType x r) else (insertType x l) + v + treeSum r

-- zeroPlus: (x: Integer) -> x = (x + 0)
-- zeroPlus 0 = Refl
-- zeroPlus x =  Refl

infixl 6 .+
-- (.+) : (Num a, Monoid a) => a -> a -> a
-- (.+) {a} x  y = case x of
--   (the a neutral) => y
--   x => case y of
--     the a neutral => x
--     y => (x + y) .+ the a neutral
(.+) : Integer -> Integer -> Integer
x .+ 0 = x
0 .+ y = y
x .+ y = (x + y) .+ 0

-- zeroPlus : (x: Integer) -> x = x .+ 0
-- zeroPlus x = ?hole1_1

interface Ttest a where
  ttt : a

implementation Ttest Integer where
  ttt = 0
--
-- fdupa : IO a
-- fdupa
--
-- hole1 : (x: Int) -> (0 + x) + 0 = x + 0
-- hole1 x = cong (zeroPlus x)
--
-- insert' : (x: Int) -> (t:Tree' n) -> Tree' (x + n)
-- insert' x Empty' = rewrite hole1 x in Node' Empty' x Empty'
-- insert' x (Node' l v r) = if (v < x) then Node' l v (insert' x r) else Node' (insert' x l) v r
--
-- listToTree' : (x: List Int) -> Tree' (sum x)
-- listToTree' [] = Empty'
-- listToTree' (x::xs) = insert' x (listToTree' xs)
--
-- same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
-- same_cons {xs} {xs} Refl = cong Refl

data Vect : Nat -> Type -> Type where
	Nil : Vect Z a
	(::) : a -> Vect k a -> Vect (S k) a
--
exactLength : (len: Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m = _} Z _ = Just []
exactLength {m = Z} (S k) [] = Nothing
exactLength {m = (S k)} (S j) (x :: y) = case (exactLength j y) of
	Nothing => Nothing
	Just v => Just (x :: v)

same_cons1 : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons1 prf = cong prf

-- same_cons2 : {xs : List a} -> x = y -> x :: xs = y :: xs
-- same_cons2 prf = cong prf

impl : {f : t -> u -> v} -> a = b -> c = d -> f a c = f b d
impl Refl Refl = Refl

same_cons :  {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_cons Refl Refl = Refl





-- allLengths : List String -> List Nat
-- allLengths [] = []
-- allLengths (x :: xs) = ?allLengths_rhs_2
