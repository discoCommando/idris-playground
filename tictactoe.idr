{-  -}

module TicTacToe
import Data.Vect
import Data.Fin

%default total

data Matrix : Nat -> Type -> Type where 
  M0 : Matrix Z a
  MR : (ms : Matrix x a) -> (lefts : Vect x a) -> (tops : Vect x a) -> (first : a) -> Matrix (S x) a

data FinDouble : Nat -> Type where 
  FD : (x : Fin k) -> (y : Fin k) -> FinDouble k

indexM : FinDouble l -> Matrix l a -> a 
indexM (FD FZ FZ) (MR ms lefts tops first) = first
indexM (FD FZ (FS y)) (MR ms lefts tops first) = index y lefts
indexM (FD (FS x) FZ) (MR ms lefts tops first) = index x tops
indexM (FD (FS x) (FS y)) (MR ms lefts tops first) = indexM (FD x y) ms

updateAtM : (i : FinDouble l) -> (f : elem -> elem) -> (xs : Matrix l elem) -> Matrix l elem
updateAtM (FD FZ FZ) f (MR ms lefts tops first) = (MR ms lefts tops $ f first)
updateAtM (FD FZ (FS y)) f (MR ms lefts tops first) = (MR ms (updateAt y f lefts) tops first)
updateAtM (FD (FS x) FZ) f (MR ms lefts tops first) = (MR ms lefts (updateAt x f tops) first)
updateAtM (FD (FS x) (FS y)) f (MR ms lefts tops first) = (MR (updateAtM (FD x y) f ms) lefts tops first)

mapMatrix : (f : elem1 -> elem2) -> (xs : Matrix l elem1) -> Matrix l elem2
mapMatrix f M0 = M0
mapMatrix f (MR ms lefts tops first) = MR (mapMatrix f ms) (map f lefts) (map f tops) (f first)

data Vector 
  = VU
  | VR 
  | VUR 
  | VUL 

sizeM : Matrix (S l) a -> Fin (S l)
sizeM (MR ms lefts tops first) = last


data StartingPoint : Matrix l a -> Vector -> FinDouble l -> Type where
  SPVU : StartingPoint m VU (FD x FZ)
  SPVR : StartingPoint m VR (FD FZ y)
  SPVUR : StartingPoint m VUR (FD FZ FZ)
  SPVUL : StartingPoint m VUL (FD Data.Fin.last FZ)

test : Matrix 2 Nat 
test = MR (MR M0 [] [] 4) [3] [2] 1 


testSPVUL : StartingPoint TicTacToe.test VUL (FD (FS FZ) FZ)
testSPVUL = SPVUL

startingPointTest : (m : Matrix 2 Nat) -> StartingPoint m v fd -> Nat
startingPointTest {v} {fd} (MR ms lefts tops first) x = ?startingPointTest_rhs_1


