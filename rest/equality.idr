module Equality

import Data.Vect

data Eeq : (f: a) -> (s : a) -> Type where
  E : (f: a) -> Eeq f f

infixl 6 ===>
(===>) : (Eeq a b) -> (f : t -> u) -> (Eeq (f a) (f b))
(E a) ===> f = E $ f a

-- infixl 6 \==>
-- (\==>) : (Eeq a b -> Void) -> Eeq b a -> Void
-- f \==> (E b) =


plusZero : (f : Nat) -> Eeq f (f + 0)
plusZero Z = E Z
plusZero (S k) = plusZero k ===> S

zeroPlus : (f : Nat) -> Eeq (f + 0) f
zeroPlus Z = E Z
zeroPlus (S k) = zeroPlus k ===> S

plusOneSymetrical : (f : Nat) -> Eeq (S f) (1 + f)
plusOneSymetrical Z = plusZero (S Z)
plusOneSymetrical (S k) = plusOneSymetrical k ===> S

onePlusSymetrical : (f : Nat) -> Eeq (1 + f) (S f)
onePlusSymetrical Z = zeroPlus (S Z)
onePlusSymetrical (S k) = onePlusSymetrical k ===> S

sameS : (x : Eeq k j) -> Eeq (S k) (S j)
sameS (E k) = E (S k)

checkEqNat : (n : Nat) -> (m : Nat) -> Maybe (Eeq n m)
checkEqNat Z Z = Just $ E Z
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
  Nothing => Nothing
  (Just x) => Just (sameS x)


exactLength: (n: Nat) -> (xs : Vect m a) -> Maybe (Vect n a)
exactLength {m} n xs = case checkEqNat m n of
  Nothing => Nothing
  Just (E m) => Just xs

zeroNotSuc : Eeq 0 (S k) -> Void
zeroNotSuc (E _) impossible

sucNotZero : Eeq (S k) 0 -> Void
sucNotZero (E _) impossible

noRec : (contra : Eeq k j -> Void) -> (Eeq (S k) (S j)) -> Void
noRec contra (E (S k)) = contra (E k)

checkEqNatDec : (n : Nat) -> (m : Nat) -> Dec (Eeq n m)
checkEqNatDec Z Z = Yes $ E 0
checkEqNatDec (S k) Z = No sucNotZero
checkEqNatDec Z (S k) = No zeroNotSuc
checkEqNatDec (S j) (S k) = case checkEqNatDec j k of
  No contra => No (noRec contra)
  Yes prf => Yes $ prf ===> S

q : (type : Type) -> (val : type) -> Type
q _ val = (=) val val

same_cons : {xs : List a} -> {ys : List a} -> Eeq xs ys -> Eeq (x :: xs) (x :: ys)
same_cons {x} (E ys) = E ys ===> (::) x

-- same_lists : {xs : List a} -> {ys : List a} -> Eeq x y -> Eeq xs  ys -> Eeq (x :: xs) (y :: ys)
-- same_lists prf1 prf2 = rewrite prf1 in same_cons prf2

same_cons' : {xs : List a} -> {ys : List a} -> xs = ys -> (x :: xs) = (x :: ys)
same_cons' Refl = Refl

same_lists' : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> (x :: xs) = (y :: ys)
same_lists' prf1 prf2 = rewrite prf1 in same_cons' prf2


data ThreeEq : a -> b -> c -> Type where
  Same : ThreeEq a a a

-- convert1 : x = y -> y = z -> ThreeEq x y z
-- convert1 Refl Refl = Same
--
-- convert2 : ThreeEq x y z -> (x = y, y = z)
-- convert2 Same = (Refl, Refl)
--
-- app : (f: t -> u) -> (a, b) -> (c, d)
-- app f (a, b) = (f a, f b)

-- allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
-- allSameS x y z = uncurry convert1 . app cong . convert2

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z Same = Same

convertFromEeq : Eeq a b -> a = b
convertFromEeq (E a) = Refl


temp : (f : Nat) -> (1 + f) = S f
temp f = convertFromEeq $ onePlusSymetrical f

temp' : (f: Nat) -> (1 + f) = S f
temp' (Z) = Refl
temp' ((S k)) = cong (temp' k)

temp'' : (f : Nat) -> S f = (1 + f)
temp'' = temp'

plusOne' : (f : Nat) -> (S f) = f + 1
plusOne' Z = Refl
plusOne' (S k) = cong (plusOne' k)

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S len} (x :: xs) =  rewrite plusOne' len in myReverse xs ++ [x]

eqZeroPlus : (k : Nat) -> k = 0 + k
eqZeroPlus Z = Refl
eqZeroPlus (S k) = cong (eqZeroPlus k)

plusZero'' : (f : Nat) -> (f + 0) = f
plusZero'' Z = Refl
plusZero'' (S k) = cong (plusZero'' k)


prf1 : (n1 : Nat) -> (n2 : Nat) -> (S (n1 + n2)) = (n1 + (S n2))
prf1 Z Z = Refl
prf1 Z (S k) = eqZeroPlus (S (S (k)))
prf1 (S k) Z = rewrite convertFromEeq (zeroPlus (S k)) in plusOne' (S k)
prf1 (S k) (S j) = cong $ prf1 k (S j)

prf2 : (n1 : Nat) -> (n2 : Nat) -> n1 + (S n2) = (S n1) + n2
prf2 Z Z = Refl
prf2 Z (S k) = Refl
prf2 (S k) Z = cong (prf2 k Z)
prf2 (S k) (S j) = cong (prf2 k (S j))


myReverse' : Vect n a -> Vect n a
myReverse' xs = reverse' [] xs where
  reverse' : Vect n a -> Vect m a -> Vect (n + m) a
  reverse' {n} acc [] = rewrite convertFromEeq (zeroPlus n) in acc
  reverse' {n} {m = (S k)} acc (x :: xs) = rewrite prf2 n  k in (reverse' (x::acc) xs)

data Tree : (a : Type) -> (length : Nat) -> Type where
  Empty : Tree a Z
  Node : a -> (left : Tree a length1) -> (right : Tree a length2) -> Tree a (S (length1 + length2))

length : Tree a k -> Nat
length {k} _ = k

add : Ord a => Tree a k -> a -> Tree a (S k)
add Empty v = Node v Empty Empty
add (Node vx left right) v = if (v > vx) then Node vx (add left v) right else rewrite prf1 (length left) (length right) in (Node vx left (add right v))

data IsInTree : a -> Tree a k -> Type where
  Here' : IsInTree a (Node a left right)
  Left : (later : IsInTree a left) -> IsInTree a (Node x left right)
  Right : (later : IsInTree a right) -> IsInTree a (Node x left right)

test : IsInTree 10 (Node 10 Empty Empty)
test = Here'

test2 : IsInTree 10 (Node 11 (Node 10 Empty Empty) Empty)
test2 = Left Here'

-- toList : Tree a k -> Vect k a
-- toList Empty = []
-- toList (Node x left right) =
--   let r = (rewrite temp'' (length right) in [x] ++ toList right)
--   in ?hole

appendTree : Ord a => Tree a k -> Tree a j -> Tree a (k + j)
appendTree x y = ?appendTree_rhs

removeElem : Ord a => (value : a) ->
  (tree : Tree a (S k)) ->
  (prf : IsInTree value tree) ->
  Tree a k

removeElem value (Node value left right) Here' = ?removeElem_rhs_1
removeElem value (Node x left right) (Left later) = ?removeElem_rhs_2
removeElem value (Node x left right) (Right later) = ?removeElem_rhs_3



fromVect : Ord a => Vect n a -> Tree a n
fromVect [] = Empty
fromVect (x :: xs) = add (fromVect xs) x

data BFactor = Minus | Zero | Plus

isValidBFactors : BFactor -> BFactor -> Bool
isValidBFactors Minus Minus = False
isValidBFactors Plus Plus = False
isValidBFactors _ _ = True

validAdd : (a : BFactor) -> (b : BFactor) -> (isValidBFactors a b = True) -> BFactor
validAdd Zero Minus Refl = Minus
validAdd Zero Plus Refl = Plus
validAdd Zero Zero Refl = Zero
validAdd Plus Zero Refl = Plus
validAdd Minus Zero Refl = Minus
validAdd Minus Plus Refl = Zero
validAdd Plus Minus Refl = Zero
validAdd Plus Plus Refl impossible
validAdd Minus Minus Refl impossible

-- data AVL : (length : Nat) -> (bfactor : BFactor) -> (a : Type) -> Type where
--   EmptyAVL : AVL Z Zero a
--   NodeAVL : a -> (left : AVL x bf1 a) -> (right : AVL y bf2 a) -> (prf : isValidBFactors bf1 bf2 = True) -> AVL (S (x + y)) (validAdd bf1 bf2 prf) a

data BiggerOrEqual : Nat -> Nat -> Type where
  ThanZero : BiggerOrEqual v Z
  Than : BiggerOrEqual k v -> BiggerOrEqual (S k) (S v)
  ThanEqual : BiggerOrEqual v v

isBiggerOrEqual : (x : Nat) -> (y : Nat) -> Maybe (BiggerOrEqual x y)
isBiggerOrEqual Z Z = Just $ ThanZero
isBiggerOrEqual Z (S k) = Nothing
isBiggerOrEqual (S k) Z = Just $ ThanZero
isBiggerOrEqual (S k) (S j) = case isBiggerOrEqual k j of
  Nothing => Nothing
  Just s => Just $ Than s

beqZeroContra : BiggerOrEqual Z (S k) -> Void
beqZeroContra (Than prf) impossible

beqStepContra : (BiggerOrEqual k j -> Void) -> BiggerOrEqual (S k) (S j) -> Void
beqStepContra contra (Than prf) = contra prf
beqStepContra contra (ThenEqual) impossible

decBiggerOrEqual : (x : Nat) -> (y : Nat) -> Dec (BiggerOrEqual x y)
decBiggerOrEqual Z Z = Yes ThanZero
decBiggerOrEqual Z (S k) = No beqZeroContra
decBiggerOrEqual (S k) Z = Yes ThanZero
decBiggerOrEqual (S k) (S j) = case decBiggerOrEqual k j of
  No contra => No $ beqStepContra contra
  Yes prf => Yes $ Than prf


data BiggestFirst : Vect (S n) Nat -> Type where
  Emp : BiggestFirst [x]
  Res : {r : Vect (S k) Nat} -> BiggerOrEqual x (head r) -> BiggestFirst (x :: r)

isBiggestFirst : (x : Vect (S k) Nat) -> Maybe (BiggestFirst x)
isBiggestFirst (x :: []) = Just $ Emp
isBiggestFirst (x :: (y :: xs)) = case isBiggerOrEqual x y of
  Nothing => Nothing
  (Just prf) => Just $ Res prf

data BiggerThanAll : (x : Nat) -> Vect n Nat -> Type where
  BEmpty : BiggerThanAll x []
  BRest : BiggerThanAll x xs -> BiggerOrEqual x y -> BiggerThanAll x (y::xs)

data IsSorted : Vect n Nat -> Type where
  Em : IsSorted []
  Re : IsSorted r -> BiggestFirst (x :: r) -> IsSorted (x :: r)
  --Al : IsSorted r -> BiggerThanAll x r -> IsSorted (x :: r)

isSorted : (v : Vect n Nat) -> Maybe (IsSorted v)
isSorted [] = Just Em
isSorted (x :: xs) = do
  sortedPrf <- isSorted xs
  biggestFirstPrf <- isBiggestFirst (x :: xs)
  pure $ Re sortedPrf biggestFirstPrf

beqContraSmaller : (BiggerOrEqual (S a) (S b) -> Void) -> BiggerOrEqual a b -> Void
beqContraSmaller contra beq = contra (Than beq)

beqFromContra : (BiggerOrEqual a b -> Void) -> BiggerOrEqual b a
beqFromContra {a = Z} {b = Z} contra impossible
beqFromContra {a = S k} {b = Z} contra impossible
beqFromContra {a = Z} {b = S k} contra = ThanZero
beqFromContra {a = S k} {b = S j} contra = Than $ beqFromContra $ beqContraSmaller contra

biggest : (v : Vect (S k) Nat) -> (x ** Elem x v)
biggest [x] = (x ** Here)
biggest (x :: (y :: xs)) =
  let (m ** prf) = biggest (y :: xs) in
  if (x > m) then
    (x ** Here)
  else
    (m ** There prf)

remove : (x : Nat) -> (v : Vect (S k) Nat) -> (Elem x v) -> Vect k Nat
remove x (x :: xs) Here = xs
remove {k = Z} x (y :: xs) (There later) impossible
remove {k = S n} x (y :: xs) (There later) = y :: remove x xs later

bubbling' : Vect (S k) Nat -> (Vect k Nat, Nat)
bubbling' x =
  let (b ** prf) = biggest x in
  (remove b x prf, b)

bubbleSort' : Vect n Nat -> Vect n Nat
bubbleSort' [] = []
bubbleSort' v@(x :: xs) =
  let (r, m) = bubbling' v in
  m :: bubbleSort' r

biggerOrEqualThanBiggerOrEqual : BiggerOrEqual x v -> BiggerOrEqual v y -> BiggerOrEqual x y
biggerOrEqualThanBiggerOrEqual beq1 ThanZero = ThanZero
biggerOrEqualThanBiggerOrEqual beq1 ThanEqual = beq1
biggerOrEqualThanBiggerOrEqual (Than prf1) (Than prf2) = Than $ biggerOrEqualThanBiggerOrEqual prf1 prf2
biggerOrEqualThanBiggerOrEqual (ThanEqual) a@(Than prf2) = a
biggerOrEqualThanBiggerOrEqual (ThanZero) (Than prf2) impossible


biggerThanBiggerThanAll : (BiggerOrEqual x v) -> (BiggerThanAll v xs) -> BiggerThanAll x xs
biggerThanBiggerThanAll beq BEmpty = BEmpty
biggerThanBiggerThanAll beq (BRest v z) =
  let beq' = (biggerOrEqualThanBiggerOrEqual beq z) in
    BRest (biggerThanBiggerThanAll beq v) beq'

biggest' : (v : Vect (S k) Nat) -> (x ** (Elem x v, BiggerThanAll x v))
biggest' [x] = (x ** (Here, BRest BEmpty $ ThanEqual))
biggest' (x :: (y :: xs)) =
  let (m ** (prf, biggers)) = biggest' (y :: xs) in
  case decBiggerOrEqual x m of
    Yes prf' => (x ** (Here, BRest (biggerThanBiggerThanAll prf' biggers) ThanEqual))
    No contra => (m ** (There prf, BRest biggers $ beqFromContra contra))

removeBiggest : (v : Vect (S k) Nat) -> (Elem x v) -> BiggerThanAll x v -> (v' : Vect k Nat ** BiggerThanAll x v')
removeBiggest (x :: xs) Here (BRest prf _) = (xs ** prf)
removeBiggest (x :: (y :: xs)) (There later) (BRest prf prfEq) =
  case removeBiggest (y :: xs) later prf of
    (v' ** prf') => ((x :: v') ** BRest prf' prfEq)

bubbling'' : (v : Vect (S k) Nat) -> (x ** v' : Vect k Nat ** BiggerThanAll x v')
bubbling'' v  =
  let (x ** (elem, bta)) = biggest' v in
    (x ** (removeBiggest v elem bta))

-- data SameSet : Vector n Nat -> Vetor n Nat -> Type where
--   SMapping : Vect n ((Nat))

-- data Set : (n : Nat) -> Type where
--   SEm : Set 0
--   S
-- surjection : {a : Vect n Nat} -> {b : Vect n Nat} -> (v1 : a) -> (v2 : b) -> Bool

-- data ForEach : (v : Vect n Nat) -> (x ** x = a) -> Type where
--   FEmpty : ForEach []

bubbleSort'' : (v : Vect n Nat) -> (v' : Vect n Nat ** IsSorted v')
bubbleSort'' [] = ([] ** Em)
bubbleSort'' v@(x :: xs) =
  let
    (max ** v' ** bta) = bubbling'' v
    (v'' ** isSortedv'') = bubbleSort'' v'
  in
    ?bubbleSort_1-- ((max :: v'') ** Al isSortedv'' bta)

minus' : Nat -> Nat -> Nat
minus' a Z = a
minus' Z a = Z
minus' (S k) (S j) = minus' k j

minusZero : (x : Nat) -> minus' x 0 = x
minusZero Z = Refl
minusZero (S k) = cong (minusZero k)

propagate : (x : Nat) -> (y : Nat) -> (x + S y = S x + y)
propagate Z Z = Refl
propagate (S k) Z = cong (propagate k Z)
propagate Z (S k) = cong (propagate Z k)
propagate (S j) (S k) = cong (propagate j (S k))

-- bubSort : (length : Nat) -> (v : Vect n Nat) ->  {v' : Vect k Nat} -> (IsSorted v') -> (length = n + k) -> (v'' : Vect length Nat ** IsSorted v'')
-- bubSort {k = k} {v' = v'} {n = Z} l [] x prf = rewrite prf in (v' ** x)
-- bubSort {k = Z} {v' = []} {n = S k} l (x :: xs) Em prf = bubSort l xs (Re {x = x} Em Emp) $ rewrite propagate k Z in prf
-- bubSort {k = S j} {v' = (y :: ys)} {n = S k} l (x :: xs) r@(Re iss bf) prf = bubSort l xs (Re {x = x} r ?hole_122) $ rewrite propagate k (S j) in prf
-- bubSort

--addAVL : Ord a => a -> AVL k bf a -> AVL

----- 9.1.6

data ElemV : a -> Vect n a -> Type where
  Her : ElemV x (x::xs)
  Ther : ElemV x xs -> ElemV x (y::xs)

tttt : ElemV 1 [1]
tttt = Her

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last ll x) -> Last (l :: ll) x

emptyContra : Last [] v -> Void
emptyContra x impossible

singularContra : (x = v -> Void) -> Last [x] v -> Void
singularContra c x impossible

bigContra : (Last xs v -> Void) -> Last (x::xs) v -> Void
bigContra f LastOne impossible
bigContra f (LastCons prf) = f prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No emptyContra
isLast [x] value = case decEq x value of
  (Yes Refl) => Yes LastOne
  (No contra) => No $ singularContra contra
isLast (x :: xs) value = case isLast xs value of
  (Yes prf) => Yes $ LastCons prf
  (No contra) => No $ bigContra contra


emptyContra' : ElemV v [] -> Void
emptyContra' x impossible

notEmptyContra : (x = v -> Void) -> (ElemV v xs -> Void) -> ElemV v (x::xs) -> Void
notEmptyContra f g Her impossible
notEmptyContra f g (Ther x) = g x

myIsElem : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (ElemV value xs)
myIsElem value [] = No emptyContra'
myIsElem value (x :: xs) = case myIsElem value xs of
  (Yes prf) => Yes $ Ther prf
  (No contra') => case decEq x value of
    (Yes Refl) => Yes Her
    (No contra) => No $ notEmptyContra contra contra'

data Odd : Nat -> Type where
  OOne : Odd (S Z)
  OMore : Odd k -> Odd (S (S k))

zeroOdd : Odd Z -> Void
zeroOdd x impossible

-- oddOdd : Odd k -> Odd (S k) -> Void
-- oddOdd OOne (OMore x) impossible
-- oddOdd (OMore x) (OMore y) = oddOdd x y
--
-- oddPlusOneOdd : (Odd (S k) -> Void) -> Odd k
-- oddPlusOneOdd {k = Z} contra impossible
-- oddPlusOneOdd {k = S x} contra = OMore ?hole_234

oddContra : (Odd k -> Void) -> Odd (S (S k)) -> Void
oddContra contra (OMore x) = contra x

isOdd : (x : Nat) -> Dec (Odd x)
isOdd Z = No zeroOdd
isOdd (S Z) = Yes OOne
isOdd (S (S k)) = case isOdd k of
  Yes prf => Yes (OMore prf)
  No contra => No $ oddContra contra

data Even : Nat -> Type where
  EOdd : (Odd k -> Void) -> Even k

zeroEvenContra : Even (S k) -> Void
zeroEvenContra (EOdd x) impossible

evenContra : (Even k -> Void) -> Even (S (S k)) -> Void
evenContra contra (EOdd evenContra) impossible

isEven : (x : Nat) -> Dec (Even x)
isEven Z = Yes $ EOdd zeroOdd
isEven (S Z) = No zeroEvenContra
isEven (S (S k)) = case isEven k of
  Yes (EOdd contra) => Yes $ EOdd $ oddContra contra
  No contra => No $ evenContra contra

addTwoOdds : Odd x -> Odd y -> Even (x + y)
addTwoOdds OOne OOne = EOdd $ oddContra zeroOdd
addTwoOdds (OMore x) OOne = case addTwoOdds x OOne of
  EOdd contra => EOdd $ oddContra contra
addTwoOdds OOne (OMore x) = case addTwoOdds OOne x of
  EOdd contra => EOdd $ oddContra contra
addTwoOdds (OMore x) (OMore y) = case addTwoOdds x (OMore y) of
  EOdd contra => EOdd $ oddContra contra

oddTemp : (Odd (S (S k)) -> Void) -> Odd k -> Void
oddTemp contra x = contra (OMore x)

plusTwo : (k : Nat) -> (j : Nat) -> k + S (S j) = S (S (k + j))
plusTwo Z Z = Refl
plusTwo (S k) Z = cong $ plusTwo k Z
plusTwo Z (S k) = cong $ plusTwo Z k
plusTwo (S k) (S j) = cong $ plusTwo k (S j)

-- proveBin : (f : Nat -> Nat -> Nat) -> (g : Nat -> Nat -> Nat) -> (k : Nat) -> (j : Nat) -> f k j = g k j
-- proveBin f g Z Z = Refl
-- proveBin f g (S k) Z = cong $ proveBin f g k Z
-- proveBin f g Z (S k) = cong $ proveBin f g Z k
-- proveBin f g (S k) (S j) = cong $ proveBin f g k (S j)


addTwoEvens : Even x -> Even y -> Even (x + y)
addTwoEvens {x = Z} {y = Z} (EOdd f) (EOdd g) = EOdd f
addTwoEvens {x = Z} {y = S k} (EOdd f) (EOdd g) = EOdd g
addTwoEvens {x = S k} {y = Z} (EOdd f) (EOdd g) = rewrite plusZero'' (S k) in EOdd f
addTwoEvens {x = S Z} {y = j} (EOdd f) (EOdd g) impossible
addTwoEvens {x = k} {y = S Z} (EOdd f) (EOdd g) impossible
addTwoEvens {x = S (S k)} {y = S (S j)} (EOdd f) (EOdd g) = case addTwoEvens (EOdd $ oddTemp f) (EOdd $ oddTemp g) of
  EOdd contra => EOdd $ oddContra $ rewrite plusTwo k j in oddContra contra

-- addEvenOdd : Even x -> Odd y -> Odd (x + y)
-- addEvenOdd {x = Z} {y = k} a b = b
-- addEvenOdd {x = S k} {y = Z} a b impossible
-- addEvenOdd {x = S (S k)} {y = S k} (EOdd f) b = OMore $ addEvenOdd (EOdd oddTemp f)
