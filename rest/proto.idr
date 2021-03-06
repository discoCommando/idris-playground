
data DoorState = DoorOpen | DoorClosed

data DoorCmd : Type -> DoorState -> DoorState -> Type where 
  Open : DoorCmd () DoorClosed DoorOpen
  Close : DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () DoorClosed DoorClosed

  Pure : t -> DoorCmd t s s 
  (>>=) : DoorCmd a s1 s2 -> (a -> DoorCmd b s2 s3) -> DoorCmd b s1 s3

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do 
  RingBell
  Open
  Close 
