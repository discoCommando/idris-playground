module Preds
import Data.Vect
import Data.Vect.Views

data BOE : Nat -> Nat -> Type where
  B0 : BOE v Z
  BT : BOE k v -> BOE (S k) (S v)

boeRContra : (BOE x y -> Void) -> BOE (S x) (S y) -> Void
boeRContra contra (BT x) = contra x

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

oddZContra : Odd (S Z) -> Void
oddZContra x impossible

oddSContra : (Odd x -> Void) -> Odd (S (S x)) -> Void
oddSContra f (OR x) = f x

isOdd : (x : Nat) -> Dec (Odd x)
isOdd Z = Yes O0
isOdd (S Z) = No oddZContra
isOdd (S (S k)) = case isOdd k of
  (Yes prf) => Yes $ OR prf 
  (No contra) => No $ oddSContra contra

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
sortedContraR contra (SorR x y) = contra x

sortedContra0 : (BOE y x -> Void) -> Sorted (y :: x :: xs) -> Void
sortedContra0 contra (SorR x y) = contra y

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

-- equalPlusZeroRight : (x : Nat) -> x = x + 0

prfNeeded' : (x : a) -> (xs : Vect n a) -> (ys : Vect j a) -> (zs : Vect i a) -> (ys ++ zs = xs) -> x :: ys ++ zs = x :: xs 
prfNeeded' x (ys ++ zs) ys zs Refl = Refl
  
vectNilLeftNeutral' : (xs : Vect n a) -> xs ++ [] = xs
vectNilLeftNeutral' [] = Refl 
vectNilLeftNeutral' (x :: xs) = 
  let prf = vectNilLeftNeutral' xs in 
  prfNeeded' x xs xs [] prf


prfNeeded : (x : a) -> (xs : Vect n a) -> (ys : Vect j a) -> (zs : Vect i a) -> (xs = ys ++ zs) -> x :: xs = x :: ys ++ zs
prfNeeded x (ys ++ zs) ys zs Refl = Refl
  
vectNilLeftNeutral : (xs : Vect n a) -> xs = xs ++ []
vectNilLeftNeutral [] = Refl 
vectNilLeftNeutral (x :: xs) = 
  let prf = vectNilLeftNeutral xs in 
  prfNeeded x xs xs [] prf

convertPer : Permutation a b -> Permutation (a ++ []) (b ++ [])
convertPer {a} {b} (Per x y) = Per (rewrite vectNilLeftNeutral' a in (rewrite vectNilLeftNeutral' b in x)) (rewrite vectNilLeftNeutral' a in (rewrite vectNilLeftNeutral' b in y))

properRemove : (v : Vect (S n) Nat) -> Elem x v -> (v' : Vect n Nat ** i : Nat ** vi : VectIndex v' i ** WithoutOne v' v x vi) 
properRemove (x :: xs) Here = (xs ** Z ** BHere ** WHere)
properRemove (y :: []) (There later) impossible
properRemove (y :: (x :: xs)) (There later) = 
  let (xs' ** i ** vi ** wo) = properRemove (x :: xs) later 
  in
  (y :: xs' ** S i ** BThere vi ** WThere wo)


-- removeTheres : Subset (a :: as) (a :: bs) -> Subset as bs
-- removeTheres (SBR el x) = ?removeTheres_rhs_1

-- removeFromSubset : (b' : Vect n Nat) -> (b : Vect (S n) Nat) -> (v : Nat) -> WithoutOne b' b v vi -> Subset (v :: a) b -> Subset a b'
-- -- removeFromSubset {v = v} {a = a} {b = (v :: b2)} {b' = b2} sub@(SBR el x) wo@WHere = 
-- --   let sub' = woSubset wo in 
-- --   ?sadsssasd
-- -- removeFromSubset {b = (y :: b)} {b' = (y :: a)} (SBR el x) (WThere z) = ?removeFromSubset_rhs_3
-- -- removeFromSubset {a=a} {b=(v :: b2)} {b'=b2} v wo@WHere (SBR el x) = 
-- --   let sub' = woSubset wo 
-- --   in ?removeFromSubset_rhs_1
-- -- removeFromSubset {a=a} {b=(y :: ys)} {b'=(y :: xs)} v (WThere z) (SBR el x) = ?removeFromSubset_rhs_2
-- -- removeFromSubset b1 (v :: b1) v WHere (SBR Here x) with (_)
-- --   removeFromSubset b1 (v :: b1) v WHere (SBR Here x) | with_pat = ?removeFromSubset_rhs_1_rhs
-- -- removeFromSubset b1 (v :: b1) v sub@WHere (SBR (There later) x) = ?hole
-- -- removeFromSubset (x :: a) (x :: b) v (WThere z) y = ?removeFromSubset_rhs_2
-- removeFromSubset b1 b v x y with (x)
--   removeFromSubset b1 (v :: b1) v x (SBR el y) | WHere = 
--     let sub' = woSubset x in
--     ?removeFromSubset_rhs_rhs_1
--   removeFromSubset (z :: a) (z :: xs) v x y | (WThere w) = ?removeFromSubset_rhs_rhs_2

removeFromPermutation : Permutation (x :: xs) ys -> WithoutOne ys' ys x vi -> Permutation xs ys'
removeFromPermutation {xs = xs} {ys = (z :: a)} {ys' = ys2} (Per (SBR el1 x) (SBR el2 w)) y with (y)
  removeFromPermutation {xs = xs} {ys = (x1 :: a)} {ys' = a} (Per (SBR el1 x) (SBR el2 w)) y | WHere = ?holee_2_rhs_1
  removeFromPermutation {xs = xs} {ys = (z :: a)} {ys' = (z :: ys)} (Per (SBR el1 x) (SBR el2 w)) y | (WThere s) = ?holee_2_rhs_2

merge' : (v1 : Vect n Nat) -> Permutation v1 a1 -> Sorted v1 ->
  (v2 : Vect j Nat) -> Permutation v2 a2 -> Sorted v2 ->
  (v3 : Vect (n + j) Nat ** (Permutation v3 (a1 ++ a2), Sorted v3))
-- merge' [] x y [] z x1 = ([] ** (Per SB0 SB0, Sor0))
-- merge' [] x y (w :: xs) z x1 = ?merge_rhs_4
-- merge' (w :: xs) x y [] z x1 = ?merge_rhs_3
-- merge' (w :: xs) x y (s :: ys) z x1 = ?merge_rhs_4
merge' {a1 = []} {a2 = a2} [] x y v2 z x1 = (v2 ** (z, x1))
merge' {a1 = a1} {a2 = []} {n} v1 x y [] z x1 = 
  ((v1 ++ []) ** (convertPer x, rewrite vectNilLeftNeutral' v1 in y))
merge' {a1 = w :: []} {a2 = (s :: [])} (w :: []) (Per (SBR Here SB0) (SBR Here SB0)) Sor1 (s :: []) (Per (SBR Here SB0) (SBR Here SB0)) Sor1 =
  case isBOE w s of 
    (Yes prf) => 
      (w :: s :: [] ** (Per (SBR Here (SBR (There Here) SB0)) (SBR Here (SBR (There Here) SB0)), SorR Sor1 prf))
    (No contra) =>  
      (s :: w :: [] ** (Per (SBR (There Here) (SBR Here SB0)) (SBR (There Here) (SBR Here SB0)), SorR Sor1 (boeFromContra contra)))

-- merge' {a1 = w :: []} {a2 = (g :: gs)} (w :: []) (Per (SBR Here SB0) (SBR Here SB0)) Sor1 (s :: (x :: xs)) (Per sub1 sub2) sor@(SorR y t) = 
--   case isBOE w s of 
--     (Yes prf) => 
--       (w :: s :: x :: xs ** (Per (SBR Here (addThere sub1)) (SBR Here (addThere sub2)), SorR sor prf))
--     (No contra) => 
--       let prf = boeFromContra contra
--       in
--       ?dasds

-- merge' {a1 = (t :: zs)} {a2 = (g :: gs)} (w :: (y :: ws)) per@(Per sub1@(SBR el x) sub2@(SBR el' x')) (SorR u v) (s :: ys) z x1 = 
--   case isBOE w s of 
--     (Yes prf) => 
--       let
--       (a1' ** i ** vi ** wo) = properRemove (t :: zs) el 
--       a = merge' {a1 = a1'} (y :: ws) ?asdas u (s :: ys) z x1 in
--       ?sdsd
--     (No contra) => ?ddsd_2

-- data Perm : (v : Vect n Nat) -> Type where 
--   Permu : 
data Subsequence : Vect n Nat -> Vect k Nat -> Type where
  Sub0 : Subsequence [] a
  SubHere : Subsequence xs ys -> Subsequence (x :: xs) (x :: ys)
  SubThere : Subsequence xs ys -> Subsequence xs (y :: ys)

data PerFromSubsequence : Vect n Nat -> Vect n Nat -> Type where 
  PerFS : Subsequence a b -> Subsequence b a -> PerFromSubsequence a b

ownSubsequence : (v : Vect n Nat) -> Subsequence v v
ownSubsequence [] = Sub0
ownSubsequence (x :: xs) = SubHere $ ownSubsequence xs

subsequenceCons : (sub1 : Subsequence a b) -> (sub2 : Subsequence b c) -> Subsequence a c 
subsequenceCons {a = []} {b = b} {c = c} Sub0 sub2 = Sub0
subsequenceCons {a = (x :: xs)} {b = (x :: ys)} {c = c} (SubHere y) sub2 with (sub2)
  subsequenceCons {a = (x :: xs)} {b = (x :: ys)} {c = (x :: zs)} (SubHere y) sub2 | (SubHere z) = SubHere $ subsequenceCons y z
  subsequenceCons {a = (x :: xs)} {b = (x :: ys)} {c = (z :: zs)} (SubHere y) sub2 | (SubThere w) = SubThere $ subsequenceCons (SubHere y) w
subsequenceCons {a = a} {b = (y :: ys)} {c = c} (SubThere x) sub2 with (sub2)
  subsequenceCons {a = a} {b = (y :: ys)} {c = (y :: xs)} (SubThere x) sub2 | (SubHere z) = SubThere $ subsequenceCons x z
  subsequenceCons {a = a} {b = (y :: ys)} {c = (z :: xs)} (SubThere x) sub2 | (SubThere w) = SubThere $ subsequenceCons (SubThere x) w 


-- mergeSort : (a : Vect n Nat) -> (v : Vect n Nat ** (PerFromSubsequence v a, Sorted v))
-- mergeSort a with (splitRec a)
--   mergeSort [] | SplitRecNil = ([] ** (Per SB0 SB0, Sor0))
--   mergeSort [x] | SplitRecOne = ([x] ** (Per (SBR Here SB0) (SBR Here SB0), Sor1))
--   mergeSort (xs ++ ys) | (SplitRecPair lrec rrec) =
--     let
--       (v1 ** (per1, sor1)) = mergeSort xs
--       (v2 ** (per2, sor2)) = mergeSort ys
--     in
--       merge' v1 per1 sor1 v2 per2 sor2

