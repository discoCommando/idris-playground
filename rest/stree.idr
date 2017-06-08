
data Integer' : Type where
  PS : Nat -> Integer'
  ZZ : Integer'
  NS : Nat -> Integer'

-- implementation Signed Integer' where
--   P Z = Zero
implementation Eq Integer' where
  (==) (PS k) (PS j) = k == j
  (==) (PS k) z = False
  (==) ZZ ZZ = True
  (==) ZZ s = False
  (==) (NS k) (NS j) = k == j
  (==) (NS k) z = False

implementation Ord Integer' where
  compare (PS k) (PS j) = compare k j
  compare (PS k) z = GT
  compare ZZ ZZ = EQ
  compare ZZ (PS j) = LT
  compare ZZ (NS j) = GT
  compare (NS k) (NS j) = compare j k
  compare (NS k) z = LT

minus : Nat -> Nat -> Integer'
minus Z Z = ZZ
minus (S x) Z = PS x
minus Z (S x) = NS x
minus (S x) (S y) = minus x y

implementation Num Integer' where
  (+) ZZ y = y
  (+) x ZZ = x
  (+) (PS x) (PS y) = PS (S(x + y))
  (+) (NS x) (NS y) = NS (S(x + y))
  (+) (PS x) (NS y) = minus x y
  (+) (NS x) (PS y) = minus y x

  (*) ZZ y = ZZ
  (*) x ZZ = ZZ
  (*) (PS x) (PS y) = PS (x * y + x + y)
  (*) (NS x) (NS y) = PS (x * y + x + y)
  (*) (PS x) (NS y) = NS (x * y + x + y)
  (*) (NS x) (PS y) = NS (x * y + x + y)

  fromInteger x = if (x == 0) then ZZ else (if (x > 0) then PS (fromInteger (x - 1)) else NS (fromInteger (x - 1)))

plusZero : (x: Integer') -> x = x + 0
plusZero ZZ = Refl
plusZero (PS x) = Refl
plusZero (NS x) = Refl

natToInteger' : (x: Nat) ->

plusOnePS : (x: Nat) -> 1 + x = x + 1 -> 1 + PS x = PS x + 1
plusOnePS Z prf = cong (prf)
plusOnePS (S x) prf = cong (prf)
-- plusOne (PS (S x)) = cong (plusOne (PS x))
-- plusOne (NS x) = Refl

plusSymetrical : (x: Integer') -> (y: Integer') -> x + y = y + x
--plusSymetrical (PS Z) y =
plusSymetrical (PS (S k)) y = cong (plusSymetrical (PS k) y)
plusSymetrical ZZ y = plusZero y
plusSymetrical (NS k) y = ?sym_4

-- (x + 1) (y + 1) = xy x y 1
-- implementation Num Integer' where
--   (+) (P x) (P y) = P (x + y)
--   (+) (NS x) (NS y) = NS (S (x + y))
--   (+) (NS x) (P Z) = NS x
--   (+) (NS Z) (P (S y)) = P y
--   (+) (NS (S x)) (P (S y)) = NS x + P y
--   (+) (P Z) (NS y) = NS y
--   (+) (P (S y)) (NS Z) = P y
--   (+) (P (S x)) (NS (S y)) = P x + NS y
--
--
--   (*) (P k) (P j) = P (k * j)
--   (*) (P k) (NS j) = NS (k * S j)
--   (*) (NS k) (P j) = NS (k * S j)
--   (*) (NS k) (NS j) = P (S k * S j)
--   fromInteger n = if (n >= 0) then P (fromInteger n) else NS (fromInteger (-n - 1))
