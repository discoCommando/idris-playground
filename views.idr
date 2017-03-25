import Data.Vect

describeList : List Int -> String
describeList [] = "Empty"
describeList (x :: xs) = "Non-empty, head = " ++ show x

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeList3 : (input : List Int) -> ListLast input -> String
describeList3 [] Empty = "Empty"
describeList3 (xs ++ [x]) (NonEmpty xs x) = "Last: " ++ show x

listLast : (input : List Int) -> ListLast input
listLast [] = Empty
listLast (x :: xs) =
  case listLast xs of
    Empty => NonEmpty [] x
    (NonEmpty xs x') => NonEmpty (x :: xs) x'

describeList5 : (input : List Int) -> String
describeList5 input with (listLast input)
  describeList5 [] | Empty = "Empty"
  describeList5 (xs ++ [x]) | (NonEmpty xs x) = "Last: " ++ show x

--is not total by idris!
myReverse : List Int -> List Int
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

data SnocList : List a -> Type where
  Empty' : SnocList []
  Snoc' : (rest : SnocList xs) -> SnocList (xs ++ [x])

snocListHelper : (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelper {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelper {input} snoc (x :: xs) =
  rewrite appendAssociative input [x] xs in snocListHelper (Snoc' snoc) xs

total
snocList : (input : List a) -> SnocList input
snocList [] = Empty'
snocList a@(x :: xs) = snocListHelper Empty' (x :: xs)

total
myReverse1 : List Int -> List Int
myReverse1 xs with (snocList xs)
  myReverse1 [] | Empty' = []
  myReverse1 (ys ++ [x]) | (Snoc' rest) = x :: (myReverse1 ys | rest)


-- data Shape
--   = Traingle Double Double
--   | Rectangle Double Double
--   | Circle Double
--
-- rectangle_area : Double -> Double -> Double
-- rectangle_area w h = width * height


data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

exact : (xs : List a) -> TakeN (xs ++ [])
exact xs = Exact xs {rest = []}

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z [] = Fewer
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
  Fewer => Fewer
  (Exact n_xs) => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)


data SnocVector : Vect n a -> Type where
  SV0 : SnocVector []
  SVR : {xs : Vect n a} -> {x : a} -> (snoc : SnocVector xs) -> SnocVector (xs ++ [x])

--
-- total
-- snocVector : (v : Vect n a) -> SnocVector v
-- snocVector {n = Z} [] = SV0
-- snocVector {n = (S len)} (x :: xs) =
--   case snocVector xs of
--     SV0 => SVR [] SV0 x
--     (SVR xs' snoc x') => SVR (x :: xs') (snocVector (x :: xs')) x'

-- snocVectorHelper : (SnocVector v1) -> (v2 : Vect n a) -> SnocVector (v1 ++ v2)
-- snocVectorHelper {v1} x [] = rewrite vectNilRightNeutral v1 in x
-- snocVectorHelper x (y :: xs) = snocVectorHelper (SVR x {x = y}) xs
--
--
-- total
-- snocVector' : (v : Vect n a) -> SnocVector v
-- snocVector' v = snocVectorHelper SV0 v
