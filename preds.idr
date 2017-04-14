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

equalPlusZeroRight : (x : Nat) -> x + 0 = x

prfNeeded : (x : a) -> (xs : Vect n a) -> (ys : Vect j a) -> (zs : Vect i a) -> (ys ++ zs = xs) -> x :: ys ++ zs = x :: xs 
prfNeeded x (ys ++ zs) ys zs Refl = Refl
  
vectNilLeftNeutral : (xs : Vect n a) -> xs ++ [] = xs
vectNilLeftNeutral [] = Refl 
vectNilLeftNeutral (x :: xs) = 
  let prf = vectNilLeftNeutral xs in 
  prfNeeded x xs xs [] prf


-- prfNeeded : (x : a) -> (xs : Vect n a) -> (ys : Vect j a) -> (zs : Vect i a) -> (xs = ys ++ zs) -> x :: xs = x :: ys ++ zs
-- prfNeeded x (ys ++ zs) ys zs Refl = Refl
  
-- vectNilLeftNeutral : (xs : Vect n a) -> xs = xs ++ []
-- vectNilLeftNeutral [] = Refl 
-- vectNilLeftNeutral (x :: xs) = 
--   let prf = vectNilLeftNeutral xs in 
--   prfNeeded x xs xs [] prf

properRemove : (v : Vect (S n) Nat) -> Elem x v -> (v' : Vect n Nat ** i : Nat ** vi : VectIndex v' i ** WithoutOne v' v x vi) 
properRemove (x :: xs) Here = (xs ** Z ** BHere ** WHere)
properRemove (y :: []) (There later) impossible
properRemove (y :: (x :: xs)) (There later) = 
  let (xs' ** i ** vi ** wo) = properRemove (x :: xs) later 
  in
  (y :: xs' ** S i ** BThere vi ** WThere wo)

-- data Subsequence : Vect n Nat -> Vect k Nat -> Type where
--   Sub0 : Subsequence [] a
--   SubHere : Subsequence xs ys -> Subsequence (x :: xs) (x :: ys)
--   SubThere : Subsequence xs ys -> Subsequence xs (y :: ys)

-- data PerFromSubsequence : Vect n Nat -> Vect n Nat -> Type where 
--   PerFS : Subsequence a b -> Subsequence b a -> PerFromSubsequence a b

-- ownSubsequence : (v : Vect n Nat) -> Subsequence v v
-- ownSubsequence [] = Sub0
-- ownSubsequence (x :: xs) = SubHere $ ownSubsequence xs

-- subsequenceCons : (sub1 : Subsequence a b) -> (sub2 : Subsequence b c) -> Subsequence a c 
-- subsequenceCons {a = []} {b = b} {c = c} Sub0 sub2 = Sub0
-- subsequenceCons {a = (x :: xs)} {b = (x :: ys)} {c = c} (SubHere y) sub2 with (sub2)
--   subsequenceCons {a = (x :: xs)} {b = (x :: ys)} {c = (x :: zs)} (SubHere y) sub2 | (SubHere z) = SubHere $ subsequenceCons y z
--   subsequenceCons {a = (x :: xs)} {b = (x :: ys)} {c = (z :: zs)} (SubHere y) sub2 | (SubThere w) = SubThere $ subsequenceCons (SubHere y) w
-- subsequenceCons {a = a} {b = (y :: ys)} {c = c} (SubThere x) sub2 with (sub2)
--   subsequenceCons {a = a} {b = (y :: ys)} {c = (y :: xs)} (SubThere x) sub2 | (SubHere z) = SubThere $ subsequenceCons x z
--   subsequenceCons {a = a} {b = (y :: ys)} {c = (z :: xs)} (SubThere x) sub2 | (SubThere w) = SubThere $ subsequenceCons (SubThere x) w 

-- merge' : (v1 : Vect n Nat) -> (per1 : PerFromSubsequence v1 a1) -> (sor1 : Sorted v1) ->
--   (v2 : Vect j Nat) -> (per2 : PerFromSubsequence v2 a2) -> (sor2 : Sorted v2) ->
--   (v3 : Vect (n + j) Nat ** (PerFromSubsequence v3 (a1 ++ a2), Sorted v3))
-- -- merge' {a1 = a1} {a2 = a2} v1 per1 sor1 v2 per2 sor2 = ?merge'_rhs
-- merge' {a1 = []} {a2 = a2} [] per1 sor1 v2 per2 sor2 = --?dds_1
--   (v2 ** (per2, sor2))
-- merge' {a1 = a1} {a2 = []} v1 per1 sor1 [] per2 sor2 = (v1 ** (per1, sor1))
-- merge' {a1 = a1} {a2 = a2} (x :: xs) per1 sor1 (y :: ys) per2 sor2 = ?merge'_rhs_3

-- mergeSort : (a : Vect n Nat) -> (v : Vect n Nat ** (PerFromSubsequence v a, Sorted v))
-- mergeSort a with (splitRec a)
--   mergeSort [] | SplitRecNil = ([] ** (PerFS Sub0 Sub0, Sor0))
--   mergeSort [x] | SplitRecOne = ([x] ** (PerFS (SubHere Sub0) (SubHere Sub0), Sor1))
--   mergeSort (xs ++ ys) | (SplitRecPair lrec rrec) =
--     let
--       (v1 ** (per1, sor1)) = mergeSort xs
--       (v2 ** (per2, sor2)) = mergeSort ys
--     in
--       merge' v1 per1 sor1 v2 per2 sor2

-- data VectIndex2 : (a : Vect n t) -> (x : Nat) -> Type where
--   BHere : (a : Vect n t) -> VectIndex a 0
--   BThere : (a : Vect n t) -> VectIndex a i -> VectIndex (x :: a) (S n)

data WithoutOneSimple : (xxs : Vect (S n) Nat) -> (xs : Vect n Nat) -> (x : Nat) -> (index : Nat) -> Type where 
  WSHere : WithoutOneSimple (x :: xs) xs x Z
  WSThere : (wo : WithoutOneSimple xxs xs x index) -> WithoutOneSimple (y :: xxs) (y :: xs) x (S index)

data PermVI : Vect n Nat -> Vect n Nat -> Type where 
  PVI0 : PermVI [] []
  PVIR : (b : Vect n Nat) -> (x : Nat) -> (per : PermVI a b) -> (wo : WithoutOneSimple xb b x index) -> PermVI (x :: a) xb

-- getIAndA : (vi : VectIndex a i) -> (a1 : Vect n Nat ** i1 : Nat ** (a1 = a, i1 = i))
-- getIAndA {a} {i} vi = (a ** i ** (Refl, Refl))

-- getBB1XAndVI : (wo : WithoutOne b b1 x vi) -> (b2 ** b3 ** x1 ** vi1 ** (b2 = b, b3 = b1, x1 = x, vi1 = vi))
-- getBB1XAndVI {b} {b1} {x} {vi} wo = (b ** b1 ** x ** vi ** (Refl, Refl, Refl, Refl))

-- -- removeVectWO : (a : Vect (S n) Nat) -> (wo : WithoutOne a1 a x vi) -> (a2 : Vect n Nat ** )

-- removeFromPermVI : (per1 : PermVI (x :: a) b) -> (b1 ** i : Nat ** vi : VectIndex b1 i ** (WithoutOne b1 b x vi, PermVI a b1))
-- removeFromPermVI {b = b} (PVIR per wo) = 
--   let 
--     (b1 ** b2 ** x ** vi ** (prf1, prf2, prf3, prf4)) = getBB1XAndVI wo 
--     (a ** i ** (prf11, prf12)) = getIAndA vi
--   in
--   (b1 ** i ** vi ** (rewrite prf1 in (rewrite prf4 in wo), rewrite prf1 in per))
  -- removeFromPermVI {b = b} a (PVIR per wo) | with_pat {b1 = b1} {vi = vi} = ?hoasd_1_rhs
-- convertPer : PermVI a b -> PermVI (a ++ []) (b ++ [])
-- -- convertPer {a} {b} (PVIR x y) = Per (rewrite vectNilLeftNeutral' a in (rewrite vectNilLeftNeutral' b in x)) (rewrite vectNilLeftNeutral' a in (rewrite vectNilLeftNeutral' b in y))
-- convertPer {a = []} {b = []} PVI0 = PVI0
-- convertPer {a = (x :: xs)} {b = b} (PVIR per wo) = ?dasdasd
  -- let wo1 = rewrite vectNilLeftNeutral b in wo in 

-- getSor : Sorted (x :: xs) -> Sorted xs
-- getSor Sor1 = Sor0
-- getSor (SorR y z) = y

-- merge' : (v1 : Vect n Nat) -> (per1 : PermVI v1 a1) -> (sor1 : Sorted v1) ->
--   (v2 : Vect j Nat) -> (per2 : PermVI v2 a2) -> (sor2 : Sorted v2) ->
--   (v3 : Vect (n + j) Nat ** (PermVI v3 (a1 ++ a2), Sorted v3))
-- merge' {a1 = []} {a2 = a2} [] PVI0 sor1 v2 per2 sor2 = (v2 ** (per2, sor2))
-- merge' {n} {a1 = a1} {a2 = []} v1 per1 sor1 [] PVI0 sor2 = (v1 ++ [] ** (convertPer per1, rewrite vectNilLeftNeutral v1 in sor1))
-- merge' {a1 = (z :: ys)} {a2 = (y :: a)} (x :: []) (PVIR w s) Sor1 (t :: []) (PVIR per wo) Sor1 = ?hole1_1
-- merge' {a1 = (z :: ys)} {a2 = (y :: a)} (x :: []) (PVIR w s) Sor1 (t :: (u :: xs)) (PVIR per wo) (SorR v x1) = ?hole1_2
-- merge' {a1 = (z :: ys)} {a2 = (y :: a)} (x :: (u :: ws)) (PVIR w s) (SorR v x1) (t :: zs) (PVIR per wo) sor2 = 
--   case isBOE x t of
--     (Yes prf) => 
--       let (v3 ** (per3, sor3)) = merge' (u :: ws) w v (t :: zs) (PVIR per wo) sor2 in
--       (x :: v3 ** (?per4, ?sor4))
--     (No contra) => 
--       let prf = boeFromContra contra in 
--       ?holee_2


-- viCons : (vi : VectIndex a i) -> (per : PermVI a b) -> (i2 ** VectIndex b i2)
-- viCons {a = []} {i = Z} {b = []} BHere PVI0 = (_ ** BHere)
-- viCons {a = (x :: xs)} {i = Z} {b = b} BHere (PVIR b2 per wo) = 
--   -- let 
--   --   (_ ** _ ** _ ** vi ** _) = getBB1XAndVI wo 
--   --   (_ ** i ** _) = getIAndA vi
--   -- in
--   (_ ** ?vi)
-- viCons {a = (x :: xs)} {i = (S k)} {b = b} (BThere y) per = ?viCons_rhs_2

-- -- woCons : WithoutOne a1 (y :: a) x vi -> WithoutOne b2 c y vi2 -> WithoutOne b2 c x vi3

data ElemWI : (x : Nat) -> (xs : Vect n Nat) -> (index : Nat) -> Type where 
  HereWI : ElemWI x (x :: xs) Z 
  ThereWI : (elwi : ElemWI x ys i) -> ElemWI x (y :: ys) (S i)

woToElemWI : (yys : Vect (S n) Nat) -> (wo : WithoutOneSimple yys ys y i) -> ElemWI y yys i
woToElemWI (y :: ys) WSHere = HereWI
woToElemWI (y :: xxs) (WSThere wo) = ThereWI $ woToElemWI xxs wo  

thereOrNotThere : (elwi : ElemWI x ys i1) -> (wo : WithoutOneSimple yys ys y i2) -> (i ** ElemWI x yys i) 
thereOrNotThere {x = x} {i1 = i1} {yys = (y :: ys)} {ys = ys} {y = y} {i2 = Z} elwi WSHere with (elwi)
  thereOrNotThere {x = x} {i1 = Z} {yys = (y :: (x :: xs))} {ys = (x :: xs)} {y = y} {i2 = Z} elwi WSHere | HereWI = (_ ** ThereWI HereWI)
  thereOrNotThere {x = x} {i1 = (S i)} {yys = (y :: (z :: xs))} {ys = (z :: xs)} {y = y} {i2 = Z} elwi WSHere | (ThereWI w) = (_ ** ThereWI (ThereWI w))
thereOrNotThere {x = x} {i1 = i1} {yys = (z :: xxs)} {ys = (z :: xs)} {y = y} {i2 = (S index)} elwi (WSThere wo) with (elwi)
  thereOrNotThere {x = x} {i1 = Z} {yys = (x :: xxs)} {ys = (x :: xs)} {y = y} {i2 = (S index)} elwi (WSThere wo) | HereWI = (_ ** HereWI)
  thereOrNotThere {x = x} {i1 = (S i)} {yys = (z :: xxs)} {ys = (z :: xs)} {y = y} {i2 = (S index)} elwi (WSThere wo) | (ThereWI w) = 
    let (_ ** elwi') = thereOrNotThere w wo in
    (_ ** ThereWI elwi')

elemPerm : (el : ElemWI x xs i) -> (per : PermVI xs ys) -> (i2 : Nat ** ElemWI x ys i2)
elemPerm {xs = (x :: xs')} {ys} {i = Z} HereWI (PVIR b x per wo) = (_ ** woToElemWI ys wo)
elemPerm {xs = (y :: xs')} {ys} {x} {i = (S k)} (ThereWI elwi) (PVIR b y per wo) = 
  let 
    (_ ** el2) = elemPerm elwi per
  in
  thereOrNotThere el2 wo 

properRemoveWOS : (xxs : Vect (S n) Nat) -> (el : ElemWI x xxs i) -> (xs : Vect n Nat ** WithoutOneSimple xxs xs x i)
properRemoveWOS (x :: xs) HereWI = (xs ** WSHere)
properRemoveWOS (y :: []) (ThereWI elwi) impossible
properRemoveWOS (y :: (x :: xs)) (ThereWI elwi) = 
  let 
    (xs' ** wo) = properRemoveWOS (x :: xs) elwi
  in 
  (y :: xs' ** WSThere wo)

-- elemPerm' : (el : ElemWI y ys i) -> (per : PermVI xs ys) -> (i2 : Nat ** ElemWI y xs i2)
-- elemPerm' el per = ?elemPerm'_rhs

-- woConsType : (i1 : Nat) -> (i2 : Nat) -> Type
-- woConsType i1 i2 = 
--   case isBOE i2 i1 of 
--     (Yes prf) => ?dsd_1
--     (No contra) => ?dsd_2
-- bxy: 0 1 x y 2 3 bx: 0 1 x 2 3 b: 0 1 2 3 iy: 3 ix: 2 by: 01y23 iy':   
-- woCons : WithoutOneSimple bxy bx y i1 -> WithoutOneSimple bx b x i2 -> (by ** WithoutOneSimple by b y i3 ** WithoutOneSimple bxy by x i4)



-- woElemWICons : (wo : WithoutOneSimple ax a x ia) -> (per : PermVI ax bx) -> (ib ** b ** WithoutOneSimple bx b x ib)
-- woElemWICons {ax} {a} {bx} wo per = ?woElemWICons_rhs

-- permReverse : (per : PermVI a b) -> PermVI b a
-- permReverse {a = []} {b = []} PVI0 = PVI0
-- permReverse {a = (x :: xs)} {b = (y :: zs)} (PVIR ys x per wo) = 
--   let 
--     -- perRev = permReverse per 
--     ely 
--   in 
--     ?permReverse_rhs_2

-- b' ** WithoutOne b' b1 y i10

data VectIndexes : (i1 : Nat) -> (i2 : Nat) -> (remi2 : Nat) -> (remi1 : Nat) -> Type where 
  V1Here : VectIndexes Z (S x) Z x
  V2Here : VectIndexes (S x) Z x Z
  -- VSame : VectIndexes (S Z) (S Z) Z Z
  VThere : VectIndexes i1 i2 remi2 remi1 -> VectIndexes (S i1) (S i2) (S remi2) (S remi1)

woRefl : (w1 : WithoutOneSimple ax a1 x i) -> (w2 : WithoutOneSimple ax a2 x i) -> a1 = a2
woRefl {ax} {a1} {a2} {i} w1 w2 with (w1)
  woRefl {ax = (x :: a1)} {a1 = a1} {a2 = a2} {i = Z} w1 w2 | WSHere with (w2)
    woRefl {ax = (x :: a1)} {a1 = a1} {a2 = a1} {i = Z} w1 w2 | WSHere | WSHere = Refl
  woRefl {ax = (y :: xxs)} {a1 = (y :: xs)} {a2 = a2} {i = (S index)} w1 w2 | (WSThere wo) with (w2)
    woRefl {ax = (y :: xxs)} {a1 = (y :: xs)} {a2 = (y :: ys)} {i = (S index)} w1 w2 | (WSThere wo) | (WSThere x) with (woRefl wo x)
      woRefl {ax = (y :: xxs)} {a1 = (y :: xs)} {a2 = (y :: xs)} {i = (S index)} w1 w2 | (WSThere wo) | (WSThere x) | Refl = Refl

woCons : (vi : VectIndexes i1 i2 i3 i4) -> 
  (woxxy : WithoutOneSimple bxy by x i1) -> 
  (woyxy : WithoutOneSimple bxy bx y i2) -> 
  (woxx : WithoutOneSimple bx b x i3) -> 
  WithoutOneSimple by b y i4
  
woCons {bxy = bxy}{bx = bx}{by = by}{b = b}{i1 = Z}{i2 = (S i4)}{i3 = Z}{i4 = i4} V1Here woxxy woyxy woxx with (woxxy)
  woCons {bxy = (x :: by)}{bx = bx}{by = by}{b = b}{i1 = Z}{i2 = (S i4)}{i3 = Z}{i4 = i4} V1Here woxxy woyxy woxx | WSHere with (woyxy)
    woCons {bxy = (x :: by)}{bx = (x :: xs)}{by = by}{b = b}{i1 = Z}{i2 = (S i4)}{i3 = Z}{i4 = i4} V1Here woxxy woyxy woxx | WSHere | (WSThere wo) with (woxx)
      woCons {bxy = (x :: by)}{bx = (x :: xs)}{by = by}{b = xs}{i1 = Z}{i2 = (S i4)}{i3 = Z}{i4 = i4} V1Here woxxy woyxy woxx | WSHere | (WSThere wo) | WSHere = wo

woCons {bxy = bxy}{bx = bx}{by = by}{b = b}{i1 = (S i3)}{i2 = Z}{i3 = i3}{i4 = Z} V2Here woxxy woyxy woxx with (woxxy)
  woCons {bxy = (y :: xxs)}{bx = bx}{by = (y :: xs)}{b = b}{i1 = (S i3)}{i2 = Z}{i3 = i3}{i4 = Z} V2Here woxxy woyxy woxx | (WSThere wo) with (woyxy)
    woCons {bxy = (y1 :: xxs)}{bx = xxs}{by = (y1 :: xs)}{b = b}{i1 = (S i3)}{i2 = Z}{i3 = i3}{i4 = Z} V2Here woxxy woyxy woxx | (WSThere wo) | WSHere with (woxx)
      woCons {bxy = (y1 :: (x :: b))}{bx = (x :: b)}{by = (y1 :: xs)}{b = b}{i1 = (S Z)}{i2 = Z}{i3 = Z}{i4 = Z} V2Here woxxy woyxy woxx | (WSThere wo) | WSHere | WSHere = 
        let prf = woRefl wo woxx in 
        rewrite prf in WSHere
      woCons {bxy = (y1 :: (y :: zs))}{bx = (y :: zs)}{by = (y1 :: xs)}{b = (y :: ys)}{i1 = (S (S index))}{i2 = Z}{i3 = (S index)}{i4 = Z} V2Here woxxy woyxy woxx | (WSThere wo) | WSHere | (WSThere x) = 
        let prf = woRefl wo woxx in 
        rewrite prf in WSHere

woCons {bxy = bxy}{bx = bx}{by = by}{b = b}{i1 = (S j)}{i2 = (S k)}{i3 = (S remi2)}{i4 = (S remi1)} (VThere x) woxxy woyxy woxx with (woxxy)
  woCons {bxy = (y :: xxs)}{bx = bx}{by = (y :: xs)}{b = b}{i1 = (S j)}{i2 = (S k)}{i3 = (S remi2)}{i4 = (S remi1)} (VThere x) woxxy woyxy woxx | (WSThere wo) with (woyxy)
    woCons {bxy = (y :: xxs)}{bx = (y :: ys)}{by = (y :: xs)}{b = b}{i1 = (S j)}{i2 = (S k)}{i3 = (S remi2)}{i4 = (S remi1)} (VThere x) woxxy woyxy woxx | (WSThere wo) | (WSThere z) with (woxx)
      woCons {bxy = (y :: xxs)}{bx = (y :: ys)}{by = (y :: xs)}{b = (y :: zs)}{i1 = (S j)}{i2 = (S k)}{i3 = (S remi2)}{i4 = (S remi1)} (VThere x) woxxy woyxy woxx | (WSThere wo) | (WSThere z) | (WSThere w) = 
        let wo' = woCons x wo z w in 
        WSThere wo'

notEqualContraCons : (i : Nat) -> (j : Nat) -> (S i = S j -> Void) -> i = j -> Void
notEqualContraCons j j f Refl = f Refl 

getVectIndexes : (i1 : Nat) -> (i2 : Nat) -> (contra : i1 = i2 -> Void) -> (i3 : Nat ** i4 : Nat ** VectIndexes i1 i2 i3 i4)
getVectIndexes Z Z contra = absurd (contra (Refl))
getVectIndexes Z (S j) contra = (_ ** _ ** V1Here)
getVectIndexes (S k) Z contra = (_ ** _ ** V2Here)
getVectIndexes (S k) (S j) contra = 
  let (_ ** _ ** vi) = getVectIndexes k j $ notEqualContraCons k j contra in 
  (_ ** _ ** VThere vi)

notEqualContraCons2 : (i : Nat) -> (j : Nat) -> (S i = S (S j) -> Void) -> i = (S j) -> Void
notEqualContraCons2 (S j) j f Refl = f Refl 

getVectIndexes2 : (i1 : Nat) -> (i4 : Nat) -> (i2 : Nat ** i3 : Nat ** VectIndexes i1 i2 i3 i4)
getVectIndexes2 Z Z = (_ ** _ ** V1Here)
getVectIndexes2 Z (S k) = (_ ** _ ** V1Here)
getVectIndexes2 (S Z) Z = (_ ** _ ** V2Here)
getVectIndexes2 (S (S k)) Z = (_ ** _ ** V2Here)
getVectIndexes2 (S k) (S j) = 
  let (_ ** _ ** vi) = getVectIndexes2 k j in 
  (_ ** _ ** VThere vi)

removeUsingWos : (vi : VectIndexes i1 i2 i3 i4) -> WithoutOneSimple axy ay x i1 -> WithoutOneSimple axy ax y i2 -> (a : Vect n Nat ** WithoutOneSimple ax a x i3) 
removeUsingWos {axy = axy}{ay = ay}{ax = ax}{i1 = Z}{i2 = (S i4)}{x = x}{y = y} V1Here wo1 wo2 with (wo1)
  removeUsingWos {axy = (x :: ay)}{ay = ay}{ax = ax}{i1 = Z}{i2 = (S i4)}{x = x}{y = y} V1Here wo1 wo2 | WSHere with (wo2)
    removeUsingWos {axy = (x :: ay)}{ay = ay}{ax = (x :: xs)}{i1 = Z}{i2 = (S i4)}{x = x}{y = y} V1Here wo1 wo2 | WSHere | (WSThere wo) = (xs ** WSHere)

removeUsingWos {axy = axy}{ay = ay}{ax = ax}{i1 = (S i3)}{i2 = Z}{x = x}{y = y} V2Here wo1 wo2 with (wo1)
  removeUsingWos {axy = (z :: xxs)}{ay = (z :: xs)}{ax = ax}{i1 = (S i3)}{i2 = Z}{x = x}{y = y} V2Here wo1 wo2 | (WSThere wo) with (wo2)
    removeUsingWos {axy = (z :: xxs)}{ay = (z :: xs)}{ax = xxs}{i1 = (S i3)}{i2 = Z}{x = x}{y = z} V2Here wo1 wo2 | (WSThere wo) | WSHere = (xs ** wo)

removeUsingWos {axy = axy}{ay = ay}{ax = ax}{i1 = (S j)}{i2 = (S k)}{x = x}{y = y} (VThere z) wo1 wo2 with (wo1)
  removeUsingWos {axy = (w :: xxs)}{ay = (w :: xs)}{ax = ax}{i1 = (S j)}{i2 = (S k)}{x = x}{y = y} (VThere z) wo1 wo2 | (WSThere wo) with (wo2)
    removeUsingWos {axy = (w :: (x :: []))}{ay = (w :: [])}{ax = (w :: [])}{i1 = (S Z)}{i2 = (S Z)}{x = x}{y = x} (VThere z) wo1 wo2 | (WSThere WSHere) | (WSThere WSHere) impossible
    removeUsingWos {axy = (w :: (t :: zs))}{ay = (w :: (u :: xs))}{ax = (w :: ys)}{i1 = (S j)}{i2 = (S k)}{x = x}{y = y} (VThere z) wo1 wo2 | (WSThere wo) | (WSThere s) = 
      let (a' ** wo') = removeUsingWos z wo s in 
      (w :: a' ** WSThere wo')

removeUsingWos2 : (vi : VectIndexes i1 i2 i3 i4) -> WithoutOneSimple axy ay x i1 -> WithoutOneSimple ay a y i4 -> (ax : Vect (S n) Nat ** WithoutOneSimple axy ax y i2)
removeUsingWos2 {i1 = Z}{i2 = (S i4)}{i4 = i4} {axy = axy}{ay = ay}{a = a}{x = x} {y = y} V1Here wo1 wo2 with (wo1)
  removeUsingWos2 {i1 = Z}{i2 = (S i4)}{i4 = i4} {axy = (x :: ay)}{ay = ay}{a = a}{x = x} {y = y} V1Here wo1 wo2 | WSHere with (wo2)
    removeUsingWos2 {i1 = Z}{i2 = (S Z)}{i4 = Z} {axy = (x :: (y :: a))}{ay = (y :: a)}{a = a}{x = x} {y = y} V1Here wo1 wo2 | WSHere | WSHere = ((x :: a) ** WSThere wo2)

    removeUsingWos2 {i1 = Z}{i2 = (S (S index))}{i4 = (S index)} {axy = (x :: (z :: xxs))}{ay = (z :: xxs)}{a = (z :: xs)}{x = x} {y = y} V1Here wo1 wo2 | WSHere | (WSThere wo) = (x :: (z :: xs) ** WSThere wo2)

removeUsingWos2 {i1 = (S i3)}{i2 = Z}{i4 = Z} {axy = axy}{ay = ay}{a = a}{x = x} {y = y} V2Here wo1 wo2 with (wo1)
  removeUsingWos2 {i1 = (S i3)}{i2 = Z}{i4 = Z} {axy = (z :: xxs)}{ay = (z :: xs)}{a = a}{x = x} {y = y} V2Here wo1 wo2 | (WSThere wo) with (wo2)
    removeUsingWos2 {i1 = (S i3)}{i2 = Z}{i4 = Z} {axy = (z :: xxs)}{ay = (z :: xs)}{a = xs}{x = x} {y = z} V2Here wo1 wo2 | (WSThere wo) | WSHere = (xxs ** WSHere)

removeUsingWos2 {i1 = (S j)}{i2 = (S k)}{i4 = (S remi1)} {axy = axy}{ay = ay}{a = a}{x = x} {y = y} (VThere z) wo1 wo2 with (wo1)
  removeUsingWos2 {i1 = (S j)}{i2 = (S k)}{i4 = (S remi1)} {axy = (w :: xxs)}{ay = (w :: xs)}{a = a}{x = x} {y = y} (VThere z) wo1 wo2 | (WSThere wo) with (wo2)
    removeUsingWos2 {i1 = (S j)}{i2 = (S k)}{i4 = (S remi1)} {axy = (w :: xxs)}{ay = (w :: xs)}{a = (w :: ys)}{x = x} {y = y} (VThere z) wo1 wo2 | (WSThere wo) | (WSThere s) = 
      let (ax ** wo') = removeUsingWos2 z wo s in 
      (w :: ax ** WSThere wo')
     
wosDec : (wo1 : WithoutOneSimple axy ay x ia) -> (wo2 : WithoutOneSimple axy ax y ib) -> Dec (ia = ib)
wosDec {ia} {ib} _ _ = decEq ia ib 

wosDec2 : (wo1 : WithoutOneSimple axy ay x ia) -> (wo2 : WithoutOneSimple ay a y ib) -> Dec (ia = (S ib))
wosDec2 {ia} {ib} _ _ = decEq ia (S ib) 

wosVectindexes2 : (wo1 : WithoutOneSimple axy ay x i1) -> (wo2 : WithoutOneSimple ay a y i4) -> (i2 : Nat ** i3 : Nat ** VectIndexes i1 i2 i3 i4)
wosVectindexes2 {i1} {i4} _ _ = getVectIndexes2 i1 i4

reverseVI : VectIndexes i1 i2 i3 i4 -> VectIndexes i2 i1 i4 i3
reverseVI V1Here = V2Here
reverseVI V2Here = V1Here
reverseVI (VThere x) = VThere $ reverseVI x

permRegression : (per : PermVI axy bxy) -> (woa : WithoutOneSimple axy ay x ia) -> (iby : Nat ** by : Vect n Nat ** wo : WithoutOneSimple bxy by x iby ** PermVI ay by)
permRegression {axy = (x :: ay)} {bxy = bxy} {ay = ay} (PVIR by x per woxby) WSHere = (_ ** _ ** woxby ** per)
permRegression {axy = (y :: xxs)} {bxy = bxy} {ay = (y :: xs)} {x} {ia = S index} (PVIR bx y per woybx) (WSThere wo) = 
  let 
    (ib ** b ** wo' ** per') = permRegression per wo
    (_ ** _ ** vi) = wosVectindexes2 woybx wo' 
    (by ** wo'') = removeUsingWos2 vi woybx wo'
    wo''' = woCons (reverseVI vi) wo'' woybx wo'
  in 
    (_ ** by ** wo'' ** PVIR b y per' wo''')

permVICons : (per1 : PermVI a b) -> (per2 : PermVI b c) -> PermVI a c
permVICons {a = []} {b = []} {c = []} PVI0 PVI0 = PVI0
permVICons {a = (x :: xs)} {b = (y :: a)} {c = c} (PVIR yawithoutX x per1 wo1) (PVIR cwithoutY y per2 wo2) = 
  let 
    (_ ** cwithoutX ** wo3' ** per'') = permRegression (PVIR cwithoutY y per2 wo2) wo1 
    pera = permVICons per1 per''
  in
  PVIR cwithoutX x pera wo3' 



mergeN : (per1 : PermVI v1 a1) -> (sor1 : Sorted v1) ->
  (per2 : PermVI v2 a2) -> (sor2 : Sorted v2) ->
  (v3 : Vect (n + j) Nat ** (PermVI v3 (a1 ++ a2), Sorted v3))
mergeN {a1 = a1} {a2 = a2} {v1 = []} {v2 = v2} per1 Sor0 per2 sor2 = ?mergeN_rhs_1
mergeN {a1 = a1} {a2 = a2} {v1 = [x]} {v2 = v2} per1 Sor1 per2 sor2 = ?mergeN_rhs_2
mergeN {a1 = a1} {a2 = a2} {v1 = (y :: (x :: xs))} {v2 = []} per1 (SorR z w) per2 Sor0 = ?mergeN_rhs_4
mergeN {a1 = a1} {a2 = a2} {v1 = (y :: (x :: xs))} {v2 = [s]} per1 (SorR z w) per2 Sor1 = ?mergeN_rhs_5
mergeN {a1 = a1} {a2 = a2} {v1 = (y :: (x :: xs))} {v2 = (s :: (t :: ys))} (PVIR b1 y per wo) (SorR z w) p2@(PVIR b2 s per1 wo1) s2@(SorR u v) = 
  case isBOE y s of 
    (Yes prf) => 
      let (v3 ** (per3, sor3)) = mergeN per z p2 s2 in
      (y :: v3 ** (?perx, SorR sor3 prf)) 
    (No contra) => ?isboe_2
    -- ?mergeN_rhs_6

mergeSort : (a : Vect n Nat) -> (v : Vect n Nat ** (PermVI v a, Sorted v))
mergeSort a with (splitRec a)
  mergeSort [] | SplitRecNil = ([] ** (PVI0, Sor0))
  mergeSort [x] | SplitRecOne = ([x] ** (PVIR [] x PVI0 WSHere, Sor1))
  mergeSort (xs ++ ys) | (SplitRecPair lrec rrec) =
    let
      (v1 ** (per1, sor1)) = mergeSort xs
      (v2 ** (per2, sor2)) = mergeSort ys
    in
      mergeN per1 sor1 per2 sor2