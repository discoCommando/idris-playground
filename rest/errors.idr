data Access = LoggedOut | LoggedIn
data PwdCheck = Correct | Incorrect
data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where 
	Password : String ->  ShellCmd PwdCheck ?pin ?pout
	Logout : ShellCmd () ?lin ?lout 
	GetSecret : ShellCmd String ?gin ?gout 
	PutStr : String -> ShellCmd () state (const state)
	Pure : String -> ShellCmd ty (state_fn res) state_fn
	(>>=) : ShellCmd a state1 state2_fn -> ((res : a) -> ShellCmd b (state2_fn res) state3_fn) ->
		ShellCmd b state1 state3_fn



data Vect : Nat -> Type -> Type where 
	Empty : Vect Z t 
	Cons : Vect n t -> t -> Vect (S n) t 

emptyVector : Vect Z Nat
emptyVector = Empty

fun : Vect n Nat -> Nat 
fun Empty = ?fun_rhs_1
fun (Cons x y) = ?fun_rhs_2


data Maybe a = Nothing | Just a 

data Maybe : Type -> Type where 
	Nothing : Maybe a 
	Just : a -> Maybe a 

data ProofThatNotEmpty : List x -> Type where 
	Prf : ProofThatNotEmpty (x :: xs) 


head : (list : List x) -> (prf : ProofThatNotEmpty list) -> x 

-- test : Vect Z t -> t 
-- test vect = fun vect

