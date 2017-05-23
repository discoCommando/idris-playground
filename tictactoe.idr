{-  -}

module TicTacToe
import Data.Vect
import Data.Fin

%default total

data Matrix : Nat -> Nat -> Type -> Type where 
  M0 : Matrix Z Z a
  MX : Vect (S m) (Vect (S n) a) -> Matrix (S n) (S m) a 

data FinDouble : Nat -> Nat -> Type where 
  FD : (x : Fin k) -> (y : Fin j) -> FinDouble k j

indexM : FinDouble n m -> Matrix n m a -> a 
indexM {n = Z} {m = Z} (FD FZ _) M0 impossible
indexM {n = Z} {m = Z} (FD (FS _) _) M0 impossible
indexM (FD x y) (MX xs) = index x (index y xs)

updateAtM : (i : FinDouble n m) -> (f : elem -> elem) -> (xs : Matrix n m elem) -> Matrix n m elem
updateAtM {n = Z} {m = Z} (FD FZ _) _ M0 impossible
updateAtM {n = Z} {m = Z} (FD (FS _) _) _ M0 impossible
updateAtM {n = (S j)} {m = (S k)} (FD x y) f (MX xs) = MX $ updateAt y (\ys => updateAt x f ys) xs 

mapMatrix : (f : elem1 -> elem2) -> (xs : Matrix n m elem1) -> Matrix n m elem2
mapMatrix {n = Z} {m = Z} f M0 = M0
mapMatrix {n = (S j)} {m = (S k)} f (MX xs) = MX $ map (map f) xs

data Vector 
  = VU
  | VR 
  | VUR 
  | VUL 

nextFinD : (m : Matrix i j a) -> (fd : FinDouble i j) -> (v : Vector) -> Maybe (FinDouble i j)
nextFinD {i = Z} {j = Z} M0 (FD FZ _) _ impossible
nextFinD {i = Z} {j = Z} M0 (FD (FS _) _) _ impossible
nextFinD {i = (S n)} {j = (S m)} (MX xs) (FD x y) VU = do 
  y' <- natToFin (S $ finToNat y) (S m)
  pure (FD x y')

nextFinD {i = (S n)} {j = (S m)} (MX xs) (FD x y) VR = do 
  x' <- natToFin (S $ finToNat x) (S n)
  pure (FD x' y)

nextFinD {i = (S n)} {j = (S m)} (MX xs) (FD x y) VUR = do 
  x' <- natToFin (S $ finToNat x) (S n)
  y' <- natToFin (S $ finToNat y) (S m)
  pure (FD x' y')

nextFinD {i = (S n)} {j = (S m)} (MX xs) (FD FZ y) VUL = Nothing
nextFinD {i = (S n)} {j = (S m)} (MX xs) (FD (FS x) y) VUL = do 
  y' <- natToFin (S $ finToNat y) (S m)
  pure (FD (weaken x) y')


-- ATTENTION!!!
-- THIS IS : 
--  _____ 
-- |1 2 3|
-- |4 5 6|
-- |7_8_9|

testMatrix3x3 : Matrix 3 3 Nat 
testMatrix3x3 = MX $ [[7, 8, 9], [4, 5 ,6], [1, 2, 3]]

data Fuel = Empty | NonEmpty (Lazy Fuel)


lineHelper : (fuel : Fuel) -> (m : Matrix i j a) -> (fd : FinDouble i j) -> (v : Vector) -> (n : Nat ** Vect n a)
lineHelper Empty m fd v = (_ ** [])
lineHelper {i = Z} {j = Z} fuel M0 (FD FZ _) _ impossible
lineHelper {i = Z} {j = Z} fuel M0 (FD (FS _) _) _ impossible
lineHelper {i = (S n)} {j = (S m)} (NonEmpty fuel) (MX xs) (FD x y) v = 
  case nextFinD (MX xs) (FD x y) v of 
    Nothing => (_ ** [indexM (FD x y) (MX xs)])
    (Just fd') => 
      let 
        (_ ** v') = lineHelper fuel (MX xs) fd' v
      in 
        (_ ** indexM (FD x y) (MX xs) :: v')

natToFuel : Nat -> Fuel 
natToFuel Z = Empty
natToFuel (S k) = NonEmpty $ natToFuel k

line : (m : Matrix i j a) -> (fd : FinDouble i j) -> (v : Vector) -> (n : Nat ** Vect n a)
line {i} {j} m fd v = lineHelper (natToFuel $ max i j) m fd v
