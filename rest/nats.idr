
data Nat' = Z' | S' Nat'

bin' : Type
bin' = Nat' -> Nat' -> Nat'

plus :  Nat' -> Nat' -> Nat'
plus Z' x = x
plus x Z' = x
plus (S' k) x = S' (plus k x)

mult :  Nat' -> Nat' -> Nat'
mult Z' x = Z'
mult x Z' = Z'
mult (S' k) x = plus k $ mult k x

fromInteger' : Integer -> Nat'
fromInteger' x = if (x <= 0) then Z' else S' (fromInteger' $ assert_smaller x $ x - 1)

implementation Num Nat' where
  (+) = plus
  (*) = mult
  fromInteger = fromInteger'

plusZero : (x : Nat') -> x = x + 0
plusZero Z' = Refl
plusZero (S' k) = Refl

plusOne : (x : Nat') -> x + 1 = 1 + x
plusOne Z' = Refl
plusOne (S' k) = cong (plusOne k)
