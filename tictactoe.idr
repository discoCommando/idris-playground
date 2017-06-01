{-  -}

module TicTacToe
import Data.Vect
import Data.Fin
import Control.Monad.State


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

data Field = Cross | Circle 

Board : Nat -> Nat -> Type  
Board i j = Matrix i j (Maybe Field)

FieldEmpty : FinDouble (S i) (S j) -> Board (S i) (S j) -> Type
FieldEmpty fd b = indexM fd b = Nothing

decFieldEmpty : (fd : FinDouble (S i) (S j)) -> (b : Board (S i) (S j)) -> Dec (FieldEmpty fd b)
decFieldEmpty {i} {j} fd b with (indexM fd b)
  decFieldEmpty {i = i} {j = j} fd b | Nothing = Yes Refl
  decFieldEmpty {i = i} {j = j} fd b | (Just x) = No $ \Refl impossible

insertToEmpty : (fd : FinDouble (S i) (S j)) -> (m : Board (S i) (S j)) -> FieldEmpty fd m -> Field -> Board (S i) (S j)
insertToEmpty fd m x field = updateAtM fd (const $ Just field) m

insertHelper : {b : Board (S i) (S j)} -> (fd : FinDouble (S i) (S j) ** x : Field ** FieldEmpty fd b) -> Board (S i) (S j)
insertHelper {b = b} (fd ** x ** prf) = insertToEmpty fd b prf x

getFromNotEmpty : (fd : FinDouble (S i) (S j)) -> (m : Board (S i) (S j)) -> (FieldEmpty fd m -> Void) -> Field
getFromNotEmpty fd m f with (indexM fd m)
  getFromNotEmpty fd m f | Nothing = absurd $ f Refl
  getFromNotEmpty fd m f | (Just x) = x 

-- data TicTacToeCmd : (ty : Type) -> (b : Board 3 3) -> (ty -> Board 3 3) -> Type where 
--   -- Pure : a -> TicTacToeCmd a b boardFn
--   (>>=) : TicTacToeCmd a b1 fn1 -> ((res: a) -> TicTacToeCmd b (fn1 res) fn2) -> TicTacToeCmd b b1 fn2 
--   Insert : TicTacToeCmd (fd : FinDouble 3 3 ** x : Field ** FieldEmpty fd b) b TicTacToe.insertHelper   
--   PutStr : String -> TicTacToeCmd () b (const b)

-- emptyBoard : Board 3 3 
-- emptyBoard = MX [[Nothing, Nothing, Nothing], [Nothing, Nothing, Nothing], [Nothing, Nothing, Nothing]]

-- insertedBoard : Board 3 3
-- insertedBoard = MX [[Nothing, Nothing, Nothing], [Nothing, Nothing, Nothing], [Just Circle, Nothing, Nothing]]


-- testCmd : TicTacToeCmd () TicTacToe.emptyBoard (const TicTacToe.emptyBoard)
-- testCmd = do
--   PutStr "dupa"
--   PutStr "a"

-- runTicTacToeCmd 


-- data BoardM : (benter : Board 3 3) -> (bexit : Board 3 3) -> (ty : Type) -> Type where
--   (>>=) : BoardM b1 b2 ty1 -> (ty1 -> BoardM b2 b3 ty2) -> BoardM b1 b3 ty2
--   Insert : (fd : FinDouble 3 3) -> (prf : FieldEmpty fd b) -> (field : Field) -> BoardM b (insertToEmpty fd b prf field) ()
--   Get : BoardM b b (Board 3 3)
--   PutStr : String -> BoardM b b ()

-- testBoardM : BoardM TicTacToe.emptyBoard TicTacToe.insertedBoard () 
-- testBoardM = 



interface BoardIface (t : Type) (fieldType : Type) (i : Nat) (j : Nat) where 
  indexB : (fd : FinDouble i j) -> t -> Maybe fieldType
  insertAtB : (fd : FinDouble i j) -> (b : t) -> (f : fieldType) -> (indexB fd b = Nothing) -> t

BoardIface (Matrix i j (Maybe Field)) Field i j where 
  indexB = indexM
  insertAtB {i = Z} {j = Z} (FD FZ _) M0 _ _ impossible
  insertAtB {i = Z} {j = Z} (FD (FS _) _) M0 _ _ impossible
  insertAtB {i = (S n)} {j = (S m)} (FD x y) (MX xs) f prf = updateAtM (FD x y) (const $ Just f) (MX xs)  

-- printBoard : (Show field, BoardIface t field i j) => t -> String 
-- printBoard {i = S k} {j = S l} x = printHelp (last {n = S k}) (last {n = S l}) x where 
--   printHelp FZ FZ x = show $ indexB (FD FZ FZ) x
--   printHelp FZ (FS y) x = ?hole_4
--   printHelp (FS y) FZ x = ?hole_1
--   printHelp (FS y) (FS z) x = ?hole_5




-- data Board : (i : Nat) -> (j : Nat) -> (fieldType : Type) -> Type where 

nextTurn : Field -> Field 
nextTurn Cross = Circle
nextTurn Circle = Cross

DefaultBoard : Type 
DefaultBoard = Matrix 3 3 (Maybe Field)

FinDoubleDefault : Type 
FinDoubleDefault = FinDouble 3 3 

record GameState where 
  constructor MkGameState 
  board : DefaultBoard
  turn : Field

data Command : Type -> Type where 
  PutStr : String -> Command ()
  GetLine : Command String 

  GetGameState : Command GameState
  GetBoard : Command DefaultBoard
  GetTurn : Command Field
  TryInsert : FinDoubleDefault -> Command (Maybe Field)  -- returns just field if there is field already. Nothing if inserted correctly 

  Pure : ty -> Command ty 
  Bind : Command ty1 -> (ty1 -> Command ty2) -> Command ty2

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b 

namespace CommandDo 
  (>>=) : Command ty1 -> (ty1 -> Command ty2) -> Command ty2
  (>>=) = Bind

namespace ConsoleDo 
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b 
  (>>=) = Do

partial
forever : Fuel
forever = NonEmpty forever

runCommand : GameState -> Command a -> IO (a, GameState)
runCommand gs (PutStr x) = do 
  putStrLn x
  pure ((), gs)
runCommand gs GetLine = do 
  str <- getLine
  pure (str, gs)
runCommand gs (Pure x) = do 
  pure (x, gs)
runCommand gs (Bind x f) = do 
  (a, gs') <- runCommand gs x 
  runCommand gs' $ f a
runCommand gs GetGameState = pure $ (gs, gs)
runCommand gs GetBoard = pure $ (board gs, gs)
runCommand gs GetTurn = pure $ (turn gs, gs)
runCommand gs (TryInsert fd) = do 
  Yes prf <- pure $ decFieldEmpty fd (board gs)
    | No contra => do
      field <- pure $ getFromNotEmpty fd (board gs) contra
      pure (Just field, gs)

  newBoard <- pure $ insertToEmpty fd (board gs) prf (turn gs)
  pure (Nothing, record {board = newBoard} gs)

run : Fuel -> GameState -> ConsoleIO a -> IO (Maybe a, GameState)
run Empty gs _ = pure (Nothing, gs)
run (NonEmpty x) gs (Quit y) = pure (Just y, gs)
run (NonEmpty x) gs (Do z f) = do 
  (res, gs') <- runCommand gs z
  run x gs' (f res)
  
data AllSame : (x : a) -> Vect n a -> Type where 
  A0 : AllSame a []
  AR : AllSame x xs -> AllSame x (x :: xs)

headDifferentContra : (y = x -> Void) -> AllSame x (y :: xs) -> Void
headDifferentContra f (AR x) = absurd (f Refl)

tailDifferentContra : (AllSame x xs -> Void) -> AllSame x (y :: xs) -> Void
tailDifferentContra f (AR x) = f x

isAllSame : DecEq a => (x : a) -> (v : Vect n a) -> Dec (AllSame x v)
isAllSame x [] = Yes A0
isAllSame x (y :: xs) with (decEq y x)
  isAllSame x (y :: xs) | (No contra) = No $ headDifferentContra contra 
  isAllSame x (y :: xs) | (Yes prf) = rewrite prf in 
    case isAllSame x xs of 
      (Yes prf') => Yes $ AR prf'
      (No contra) => No $ tailDifferentContra contra

DecEq Field where 
  decEq Cross Cross = Yes Refl
  decEq Circle Circle = Yes Refl

  decEq Cross Circle = No $ \Refl impossible
  decEq Circle Cross = No $ \Refl impossible

isWinningLine : (l : Nat) -> (field : Field) -> (n : Nat ** Vect n (Maybe Field)) -> Bool
isWinningLine l field (n ** v) = 
  case decEq l n of 
    (No contra) => False 
    (Yes prf) => case isAllSame (Just field) v of 
      (Yes prf) => True
      (No contra) => False

WinningLine : DefaultBoard -> Field -> Type
WinningLine b field = (fd : FinDouble 3 3 ** vector : Vector ** (isWinningLine 3 field (line b fd vector) = True))

findWinningLineHelper : (fuel : Fuel) -> (b : DefaultBoard) -> (field : Field) -> (fd : FinDouble 3 3) -> (v : Vector) -> Maybe (WinningLine b field)
findWinningLineHelper (NonEmpty fuel) b field fd v =
  case decEq (isWinningLine 3 field (line b fd v)) True of 
    (Yes prf) => Just $ (fd ** v ** prf)
    (No contra) => case fd of 
      (FD FZ FZ) => Nothing
      (FD FZ (FS y)) => findWinningLineHelper fuel b field (FD FZ $ weaken y) v
      (FD (FS x) y) => findWinningLineHelper fuel b field (FD (weaken x) y) v
findWinningLineHelper Empty _ _ _ _ = Nothing
  
firstJust : Vect n (Lazy (Maybe a)) -> Maybe a    
firstJust [] = Nothing
firstJust (Nothing :: xs) = firstJust xs
firstJust ((Just x) :: xs) = Just x

findWinningLine : (b : DefaultBoard) -> (field : Field) -> Maybe (WinningLine b field)
findWinningLine b field = 
  let 
    fuel = natToFuel (3 * 3) 
    maxFd = FD last last
  in 
    firstJust 
      [ Delay $ findWinningLineHelper fuel b field maxFd VU
      , Delay $ findWinningLineHelper fuel b field maxFd VR
      , Delay $ findWinningLineHelper fuel b field maxFd VUR
      , Delay $ findWinningLineHelper fuel b field maxFd VUL
      ] 

Show Field where 
  show Cross = "O"
  show Circle = "X"

Show DefaultBoard where 
  show m = "Hell"


ticTacToe : ConsoleIO GameState
ticTacToe = do
  gs <- GetGameState
  PutStr $ show (board gs) 
  PutStr $ "Turn: " ++ show (turn gs)
  Quit gs

emptyBoard : DefaultBoard
emptyBoard = MX [[Nothing, Nothing, Nothing], [Nothing, Nothing, Nothing], [Nothing, Nothing, Nothing]]

partial
main : IO ()
main = do 
  (Just gs, gs') <- run forever (MkGameState emptyBoard Circle) ticTacToe
    | _ => putStrLn "ran out of fuel"
  pure ()
