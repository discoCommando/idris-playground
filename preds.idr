module Preds
import Data.Vect
import Data.Vect.Views

data BOE : Nat -> Nat -> Type where
  B0 : BOE v Z
  BT : BOE k v -> BOE (S k) (S v)

boeRContra : (BOE x y -> Void) -> BOE (S x) (S y) -> Void
boeRContra contra (BT x) impossible

boeZContra : BOE Z (S y) -> Void
boeZContra B0 impossible
boeZContra (BT _) impossible

isBOE : (a : Nat) -> (b : Nat) -> Dec (BOE a b)
isBOE v Z = Yes B0
isBOE Z (S v) = No $ boeZContra
isBOE (S i) (S j) = case isBOE i j of
  Yes prf => Yes $ BT prf
  No contra => No $ boeRContra contra

boeFromContra : (BOE a b -> Void) -> BOE b a
boeFromContra {a = Z} contra = B0
boeFromContra {a = (S k)} {b = S j} contra = BT $ boeFromContra $ contra . BT

data ForEvery : (v : Vect n Nat) -> (f : Nat -> Type) -> Type where
  F0 : ForEvery [] f
  FR : {f : Nat -> Type} -> (x : Nat) -> (valOfType : f x) -> (fe : ForEvery xs f) -> ForEvery (x :: xs) f

infixl 9 |>
(|>) : a -> (a -> b) -> b
a |> f = f a

bf0 : Nat -> Type
bf0 x = BOE x 0

test : ForEvery [1, 2] Preds.bf0
test = F0 |>
  FR 2 B0 |>
  FR 1 B0

data Odd : Nat -> Type where
  O0 : Odd Z
  OR : Odd k -> Odd (S (S k))

test' : ForEvery [2, 4] Odd
test' = F0 |>
  FR 4 (OR O0 |> OR) |>
  FR 2 (OR O0)

howMany : Nat -> Vect n Nat -> Nat
howMany x [] = 0
howMany x (y::ys) = case decEq x y of
  Yes _ => S (howMany x ys)
  No _ => howMany x ys

eq1Type : Vect n Nat -> Nat -> Type
eq1Type a x = (howMany x a = 1)

data ExactlyOne : (a : Vect n Nat) -> (b : Vect k Nat) -> Type where
  EO : ForEvery a (eq1Type b) -> ExactlyOne a b

exactlyOne1contra : (howMany x b = 1 -> Void) -> ExactlyOne (x :: xs) b -> Void
exactlyOne1contra contra (EO x) impossible

exactlyOneRcontra : (ExactlyOne xs b -> Void) -> ExactlyOne (x :: xs) b -> Void
exactlyOneRcontra contra (EO x) impossible

isExactlyOne : (a : Vect n Nat) -> (b : Vect k Nat) -> Dec (ExactlyOne a b)
isExactlyOne {n = Z} [] b = Yes $ EO F0
isExactlyOne {n = S k} (x::xs) b = case decEq (howMany x b) 1 of
  (Yes deprf) => case isExactlyOne xs b of
    (Yes (EO fe)) => Yes $ EO $ FR x deprf fe
    (No contra) => No $ exactlyOneRcontra contra
  (No contra) => No $ exactlyOne1contra contra

data Distinct : (a : Vect n Nat) -> Type where
  DD : ExactlyOne a a -> Distinct a

isDistinctContra : (ExactlyOne a a -> Void) -> Distinct a -> Void
isDistinctContra contra (DD x) impossible

isDistinct : (a : Vect n Nat) -> Dec (Distinct a)
isDistinct xs = case isExactlyOne xs xs of
  Yes prf => Yes $ DD prf
  No contra => No $ isDistinctContra contra

data Subsequence : (a : Vect j Nat) -> (b : Vect k Nat) -> Type where
  SQ0 : Subsequence [] xs
  SQHere : Subsequence a b -> Subsequence (x :: a) (x :: b)
  SQThere : Subsequence a b -> Subsequence a (x :: b)

sqHereContra : (Subsequence a b -> Void) -> Subsequence (x :: a) (x :: b) -> Void
sqHereContra f (SQHere x) = f x
sqHereContra f (SQThere x) impossible

sqThereContra : (Subsequence (x :: a) b -> Void) -> Subsequence (x :: a) (y :: b) -> Void
sqThereContra f (SQHere x) impossible
sqThereContra f (SQThere x) = f x

sq0Contra : Subsequence (x :: a) [] -> Void
sq0Contra s impossible

isSubsequence : (a : Vect j Nat) -> (b : Vect k Nat) -> Dec (Subsequence a b)
isSubsequence {j = Z} {k = x} [] b = Yes SQ0
isSubsequence {j = S x} {k = Z} (a :: as) [] = No sq0Contra
isSubsequence {j = S j'} {k = S k'} (x :: xs) (y :: ys) =
  case decEq x y of
    Yes deprf => case isSubsequence xs ys of
      Yes sqprf => Yes $ rewrite deprf in SQHere sqprf
      No contra => No $ rewrite deprf in sqHereContra contra
    No contra1 => case isSubsequence (x :: xs) ys of
      Yes sqprf => Yes $ SQThere sqprf
      No contra => No $ sqThereContra contra

data BiggerThanFirst : (x : Nat) -> (v : Vect n Nat) -> Type where
  BF0 : BiggerThanFirst x []
  BFR : (x : Nat) -> (v : Vect (S n) Nat) -> BOE x (head v) -> BiggerThanFirst x v

biggerThanFirstContra : (BOE x v -> Void) -> BiggerThanFirst x (v :: vs) -> Void
biggerThanFirstContra contra (BFR x v c) impossible

isBiggerThanFirst : (x : Nat) -> (v : Vect n Nat) -> Dec (BiggerThanFirst x v)
isBiggerThanFirst x [] = Yes BF0
isBiggerThanFirst x (v::vs) = case isBOE x v of
  Yes prf => Yes $ BFR x (v :: vs) prf
  No contra => No ?contra2

data Sorted : (v : Vect n Nat) -> Type where
  Sor0 : Sorted []
  Sor1 : Sorted [x]
  SorR : Sorted (x :: xs) -> BOE y x -> Sorted (y :: x :: xs)

sortedContraR : (Sorted xs -> Void) -> Sorted (x :: xs) -> Void
sortedContraR contra (SorR x y) impossible

sortedContra0 : (BOE y x -> Void) -> Sorted (y :: x :: xs) -> Void
sortedContra0 contra (SorR x y) impossible

isSorted : (v : Vect n Nat) -> Dec (Sorted v)
isSorted {n = Z} [] = Yes Sor0
isSorted {n = S Z} [x] = Yes Sor1
isSorted {n = (S (S k))} (y :: x :: xs) = case isSorted (x :: xs) of
  Yes prf => case isBOE y x of
    Yes prf2 => Yes $ SorR prf prf2
    No contra => No $ sortedContra0 contra
  No contra => No $ sortedContraR contra

data Subset : (a : Vect i Nat) -> (b : Vect j Nat) -> Type where
  SB0 : Subset [] b
  SBR : (el : Elem x b) -> Subset a b -> Subset (x :: a) b

data Permutation : (a : Vect i Nat) -> (b : Vect i Nat) -> Type where
  Per : Subset a b -> Subset b a -> Permutation a b

data VectIndex : (a : Vect n t) -> (x : Nat) -> Type where
  BHere : VectIndex a Z
  BThere : VectIndex a n -> VectIndex (x :: a) (S n)

data WithoutOne : (a : Vect n t) -> (b : Vect (S n) t) -> (x : t) -> (vi : VectIndex a i) -> Type where
  WHere : WithoutOne xs (x :: xs) x BHere
  WThere : WithoutOne a b y vi -> WithoutOne (x :: a) (x :: b) y (BThere vi)

properInsert : (a : Vect n Nat) -> (vi : VectIndex a i) -> (x : Nat) -> (b ** WithoutOne a b x vi)
properInsert a BHere x = ((x :: a) ** WHere)
properInsert (y :: xs) (BThere z) x =
  let (a ** wo) = properInsert xs z x in
  ((y :: a) ** WThere wo)

-- INSERT

woToElem : WithoutOne a b x c -> Elem x b
woToElem WHere = Here
woToElem (WThere y) = There $ woToElem y

insertA : (s : Subset v' v) -> Subset v' (a :: v)
insertA SB0 = SB0
insertA (SBR el s)  = SBR (There el) $ insertA s

insertRight : {v' : Vect n Nat} -> (s : Subset v' (a :: v)) -> (vi : VectIndex v' i) -> (v'' : Vect (S n) Nat ** (Subset v'' (a :: v), WithoutOne v' v'' a vi))
insertRight {a = a} {v' = v'} {i = Z} s BHere = ((a :: v') ** (SBR Here s, WHere))
insertRight {a = a} {i = (S k)} {v' = (t :: ts)} (SBR el s) (BThere later) =
  let (v'' ** (ss, wo)) = insertRight {v' = ts} s later in
  ((t :: v'') ** (SBR el ss, WThere wo))

addThere : (s : Subset a b) -> Subset a (x :: b)
addThere SB0 = SB0
addThere (SBR el y) = SBR (There el) $ addThere y

getSubsetEl : (el : Elem x b) -> (s : Subset b c) -> Elem x c
getSubsetEl {b = (x :: xs)} Here (SBR el s) = el
getSubsetEl {b = (y :: xs)} (There later) (SBR el s) = getSubsetEl later s

subsetCons : (s1 : Subset a b) -> (s2 : Subset b c) -> Preds.Subset a c
subsetCons SB0 s2 = SB0
subsetCons (SBR el y) s2 = SBR (getSubsetEl el s2) $ subsetCons y s2

sameVSubset : (a : Vect n Nat) -> Subset a a
sameVSubset [] = SB0
sameVSubset (a :: as) = SBR Here $ addThere $ sameVSubset as

woSubset : (wo : WithoutOne a b x vi) -> Subset a b
woSubset {a = a} {b = (x :: a)} WHere = addThere $ sameVSubset a
woSubset {a = (x :: ys)} {b = (x :: xs)} (WThere y) = SBR Here $ addThere $ woSubset y

subsetWOHelper : (s : Subset a b) -> (wo : WithoutOne b v' x vi) -> Subset a v'
subsetWOHelper s wo =
  let swo = woSubset wo in
  subsetCons s swo

subsetWO : (s : Subset a b) -> (wo : WithoutOne b v' x vi) -> Subset (x :: a) v'
subsetWO s wo = SBR (woToElem wo) $ subsetWOHelper s wo

insert : (per : Permutation sorted original) -> (max : Nat) -> (vi : VectIndex original i) -> (originalWithMax ** (Permutation (max :: sorted) originalWithMax, WithoutOne original originalWithMax max vi))
insert (Per s1 s2) a index =
  let
    s2' = insertA s2 {a = a}
    (v'' ** (s2'', wo)) = insertRight s2' index
    s1' = subsetWO s1 wo
  in
  (v'' ** (Per s1' s2'', wo))

-- BIGGEST

-- BTA - bigger than all

data BTA : (x : Nat) -> (v : Vect n Nat) -> Type where
  BTA0 : BTA x []
  BTAR : (boe : BOE x y) -> (bta : BTA x v) -> BTA x (y :: v)

--biggest : (a : Vect (S n) Nat) -> ((x, a', vi) : (Nat, Vect n Nat, VectIndex a i) ** (WithoutOne a' a x vi, BTA x a'))

boeCons : BOE x y -> BOE y z -> BOE x z
boeCons b1 B0 = B0
boeCons (BT y) (BT x) = BT $ boeCons y x

btaCons : BTA x xs -> BOE y x -> BTA y xs
btaCons BTA0 b2 = BTA0
btaCons (BTAR x z) b2 = BTAR (boeCons b2 x) (btaCons z b2)

btaWO : BTA bigg a' -> BOE x bigg -> BTA x a'
btaWO BTA0 boe = BTA0
btaWO (BTAR B0 z) a = BTAR B0 $ btaWO z a
btaWO (BTAR x z) y = BTAR (boeCons y x) $ btaWO z y

btaBOE : WithoutOne a' a bigg vi -> BTA x a' -> BOE x bigg -> BTA x a
btaBOE WHere bta boe = BTAR boe bta
btaBOE (WThere z) (BTAR boe' bta) boe = BTAR boe' $ btaBOE z bta boe

btaWOBOE : WithoutOne a' a bigg vi -> BTA bigg a' -> BOE x bigg -> BTA x a
btaWOBOE wo bta boe =
  let
    bta' = btaWO bta boe
    bta'' = btaBOE wo bta' boe
  in
    bta''

biggest : (a : Vect (S n) Nat) -> (x ** a' : Vect n Nat ** i ** vi : VectIndex a' i ** wo : WithoutOne a' a x vi ** BTA x a')
biggest {n = Z} (x :: []) = (x ** [] ** Z ** BHere ** WHere ** BTA0)
biggest {n = S k} (x :: (y :: xs)) =
  let (bigg ** a' ** i ** vi ** wo ** bta) = biggest (y :: xs) in
  case isBOE bigg x of
    (Yes prf) => (bigg ** (x :: a') ** S i ** BThere vi ** WThere wo ** BTAR prf bta)
    (No contra) => (x ** y :: xs ** Z ** BHere ** WHere ** btaWOBOE wo bta $ boeFromContra contra) --btaCons bta $ boeFromContra contra

-- SELECTION SORT

-- headSor : {v : Vect (S n) Nat} -> Sorted v -> (x : Nat ** v' : Vect n Nat ** WithoutOne v' v x BHere)
-- headSor {v = [x]} Sor1 = (x ** [] ** WHere)
-- headSor {v = (y :: (x :: xs))} (SorR z w) = (y ** (x :: xs) ** WHere)

permutationCons : Permutation a b -> Permutation b c -> Permutation a c
permutationCons (Per x z) (Per y w) = Per (subsetCons x y) (subsetCons w z)

woOriginalEqual : WithoutOne a b el vi -> WithoutOne a c el vi -> b = c
woOriginalEqual {b = (el :: a)} {c = (el :: a)} WHere WHere = Refl
woOriginalEqual {b = (x :: xs)} {c = (x :: b)} (WThere z) (WThere y) = cong (woOriginalEqual z y)

swapPermutation : Permutation a b -> Permutation b a
swapPermutation (Per x y) = Per y x

sortedBTA : (sor : Sorted xs) -> (bta : BTA x xs) -> Sorted (x :: xs)
sortedBTA {xs = []} Sor0 bta = Sor1
sortedBTA {xs = (y :: ys)} sor (BTAR boe bta) = SorR sor boe

-- boeSubset : (boe : BOE x y)
boeSubset : (bta : BTA x a) -> (el : Elem y a) -> BOE x y
boeSubset (BTAR boe bta) Here = boe
boeSubset (BTAR boe bta) (There later) = boeSubset bta later

btaSubset : (bta : BTA x a) -> (s : Subset b a) -> BTA x b
btaSubset {b = []}        bta  SB0       = BTA0
btaSubset {b = (w :: a)}  bta  (SBR el s) = BTAR (boeSubset bta el) $ btaSubset bta s

selectionSort : (a : Vect n Nat) -> (v : Vect n Nat ** (Permutation v a, Sorted v))
selectionSort {n = Z} [] = ([] ** (Per SB0 SB0, Sor0))
selectionSort {n = S Z} [x] = ([x] ** (Per (SBR Here SB0) (SBR Here SB0), Sor1))
selectionSort {n = S (S k)} (x :: y :: xs) =
  let
    (m ** a' ** i ** vi ** wo ** bta) = biggest (x :: y :: xs)
    (sorteda' ** (Per s1 s2, sor)) = selectionSort a'
    (a''' ** (per', wo')) = insert (Per s1 s2) m vi
    prf = woOriginalEqual wo wo'
  in
    (m :: sorteda' ** (rewrite prf in per', sortedBTA sor $ btaSubset bta s1))

merge' : (v1 : Vect n Nat) -> Permutation v1 a1 -> Sorted v1 ->
  (v2 : Vect j Nat) -> Permutation v2 a2 -> Sorted v2 ->
  (v3 : Vect (n + j) Nat ** (Permutation v3 (a1 ++ a2), Sorted v3))
merge' [] (Per x w) y v2 z x1 = ?merge'_rhs_3
merge' (w :: xs) x y v2 z x1 = ?merge'_rhs_2


mergeSort : (a : Vect n Nat) -> (v : Vect n Nat ** (Permutation v a, Sorted v))
mergeSort a with (splitRec a)
  mergeSort [] | SplitRecNil = ([] ** (Per SB0 SB0, Sor0))
  mergeSort [x] | SplitRecOne = ([x] ** (Per (SBR Here SB0) (SBR Here SB0), Sor1))
  mergeSort (xs ++ ys) | (SplitRecPair lrec rrec) =
    let
      (v1 ** (per1, sor1)) = mergeSort xs
      (v2 ** (per2, sor2)) = mergeSort ys
    in
      merge' v1 per1 sor1 v2 per2 sor2
