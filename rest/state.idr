

data State : (stateType : Type) -> Type -> Type where 
	Get : State stateType stateType
	Set : stateType -> State stateType () 

	Pure : ty -> State stateType () 
	(>>=) : State stateType ty1 -> (ty1 -> State stateType ty2) -> State stateType ty2

