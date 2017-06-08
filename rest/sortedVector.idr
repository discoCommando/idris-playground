module SortedVect
import Data.Vect

biggerNat : Nat -> Nat -> Nat
biggerNat Z s = s
biggerNat s Z = s
biggerNat (S k) (S j) = S $ biggerNat k j


data MaxVect : (length : Nat) -> (max : Nat) -> Type where
  ME : MaxVect 0 0
  MC : (a : Nat) -> MaxVect l max -> MaxVect (S l) (biggerNat a max)

data ElemM : MaxVect (S l) m -> (max : Nat) -> Type where
  HereM : ElemM (MC m xs) m
  ThereM : ElemM xs m -> ElemM (MC x xs) m

data Dupa : (f : Type) -> f -> Type where
  MkDupa : {a : f} -> Dupa f a


-- data ElemGen : (f : Nat -> Nat -> Type) ->
--   (fun : (a : Nat) -> f (S l) m -> f (S (S l)) (biggerNat a b)) ->
--   f (S l) m ->
--   (max : Nat) ->
--   Type where
--
--   HereGen : {f : Nat -> Nat -> Type} -> {v : f (S l) m} -> ElemGen f fun v m
--   ThereGen : ElemGen f fun xs m -> ElemGen f fun (fun x xs) m

-- test : ElemGen MaxVect MC (MC 1 ME) 1
-- test = HereGen
--
-- test2 : ElemGen MaxVect MC (MC 1 (MC 2 ME)) 2
-- test2 = ThereGen MC HereGen
--
-- test3 : ElemM (MC 1 (MC 2 ME)) 2
-- test3 = ThereM HereM

toMaxVect : Vect n Nat -> (m ** MaxVect n m)
toMaxVect [] = (0 ** ME)
toMaxVect (x :: xs) =
  let (m' ** mv) = toMaxVect xs in
    (biggerNat x m' ** MC x mv)

data BOE : Nat -> Nat -> Type where
  B0 : BOE v Z
  BT : BOE k v -> BOE (S k) (S v)
  --ThanEqual : BOE v v

boeZeroContra : BOE Z (S k) -> Void
boeZeroContra B0 impossible
boeZeroContra (BT x) impossible

boeStepContra : (BOE a b -> Void) -> BOE (S a) (S b) -> Void
boeStepContra contra (BT x) = contra x

boe : (a : Nat) -> (b : Nat) -> Dec (BOE a b)
boe a Z = Yes B0
boe Z (S j) = No boeZeroContra
boe (S k) (S j) = case boe k j of
  (Yes prf) => Yes $ BT prf
  (No contra) => No $ boeStepContra contra

boeFromContra : (BOE a b -> Void) -> BOE b a
boeFromContra {a = Z} contra = B0
boeFromContra {a = (S k)} {b = S j} contra = BT $ boeFromContra $ contra . BT

boeEqual : BOE a b -> BOE b a -> a = b
boeEqual B0 B0 = Refl
boeEqual (BT x) (BT y) = cong (boeEqual x y)

data SortedVect : (length : Nat) -> (max : Nat) -> Type where
  SE : SortedVect 0 0
  SC : (a : Nat) -> SortedVect l max -> BOE a max -> SortedVect (S l) a

-- insert : (a : Nat) -> (sv : SortedVect l m) -> (nm ** SortedVect (S l) nm)
-- insert a SE = (a ** SC a SE B0)
-- insert {l = S k} {m = m} a sv@(SC m x y) = case boe a m of
--   (Yes prf) => (a ** SC a sv prf)
--   (No contra) =>
--     let (newMax ** (SC newMax sv' prf)) = insert a x in
--
--       --   (Yes prf') => (m ** SC m (SC newMax sv' prf) (boeFromContra $  ?contra1))
--       --   (No contra) => (m ** SC m sv' ?y_1)
--       case decEq newMax a of
--         (Yes prf') => (m ** SC m (SC newMax sv' prf) $ boeFromContra $   rewrite prf' in contra)
--         (No contra) =>
--           case decEq newMax y' of
--             (Yes prf') => (m ** SC m (SC newMax sv' prf) (rewrite prf' in y))
--             (No contra') impossible
          --
bubSort :
  (length : Nat) ->
  (v : Vect n Nat) ->
  (sv : SortedVect k max) ->
  (prf : length = n + k) ->
  (m : Nat ** SortedVect length m)
bubSort {k = k} {max = max} l [] sv prf = rewrite prf in (max ** sv)
bubSort l (x :: xs) SE prf = ?hole_3
bubSort l (x :: xs) (SC max' y z) prf = ?hole_4

-- bubbleSort : (v : Vect n Nat) -> (m : Nat ** SortedVect n m)
-- bubbleSort v = ?hole_123

-- swap :

bubbleSort' : (v : MaxVect l m) -> SortedVect l m
bubbleSort' ME = SE
-- bubbleSort' (MC a )
mutual

  data SV : (length : Nat) -> Type where
    SV0 : SV Z
    SV1 : (a : Nat) -> SV (S Z)
    SVR : (a : Nat) -> (xs : SV (S k)) -> BOE a (firstSV xs) -> SV (S (S k))

  firstSV : SV (S k) -> Nat
  firstSV (SV1 a) = a
  firstSV (SVR a _ _) = a

sv : Vect n Nat -> DecEq (SV n)
sv [] = Yes SV0
sv [a] = Yes $ SV1 a
sv (x :: x' :: xs) = case boa x x' of
  Yes prf => ?hell
  No contra => No 
