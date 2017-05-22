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

-- test : Matrix 2 Nat 
-- test = MR (MR M0 [] [] 4) [3] [2] 1 


-- testSPVUL : StartingPoint TicTacToe.test VUL (FD (FS FZ) FZ)
-- testSPVUL = SPVUL


-- is not total, have no idea why
-- startingPointTest : (m : Matrix 2 Nat) -> StartingPoint m v fd -> Nat
-- startingPointTest {v = VU} {fd = (FD x FZ)} (MR ms lefts tops first) SPVU = ?startingPointTest_rhs_2
-- startingPointTest {v = VR} {fd = (FD FZ y)} (MR ms lefts tops first) SPVR = ?startingPointTest_rhs_3
-- startingPointTest {v = VUR} {fd = (FD FZ FZ)} (MR ms lefts tops first) SPVUR = ?startingPointTest_rhs_4
-- startingPointTest {v = VUL} {fd = (FD (FS FZ) FZ)} (MR ms lefts tops first) SPVUL = ?startingPointTest_rhs_5
-- startingPointTest _ _ = ?startingPointTest_rhs_1

nextFinD : (m : Matrix l a) -> (fd : FinDouble l) -> (v : Vector) -> Maybe (FinDouble l)
nextFinD {l = l} m (FD x y) VU = do
  y' <- natToFin (S $ finToNat y) l 
  pure (FD x y') 

nextFinD {l = l} m (FD x y) VR = do
  x' <- natToFin (S $ finToNat x) l 
  pure (FD x' y)

nextFinD {l = l} m (FD x y) VUR = do
  x' <- natToFin (S $ finToNat x) l
  y' <- natToFin (S $ finToNat y) l
  pure (FD x' y')
  
nextFinD {l = (S k)} m (FD FZ y) VUL = Nothing
nextFinD {l = (S k)} m (FD (FS x) y) VUL = do 
  y' <- natToFin (S $ finToNat y) (S k)
  pure (FD (weaken x) y')

-- line : (m : Matrix l a) -> (fd : FinDouble l) -> (v : Vector) -> (n : Nat ** Vect n a)
-- line m fd v = 
--     case nextFinD m fd v of 
--       Nothing => (_ ** [indexM fd m])
--       (Just fd') => 
--         let 
--           (_ ** v') = line m fd' v 
--         in 
--           (_ ** indexM fd m :: v')
  
--   
