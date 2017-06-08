
import System.Concurrency.Channels
 
data Message = Add Nat Nat

data MessagePID = MkMessage PID

data Process : Type -> Type where 
	Action : IO a -> Process a 
	Pure : a -> Process a 
	(>>=) : Process a -> (a -> Process b) -> Process b
	Spawn : Process () -> Process (Maybe MessagePID)
	Request : MessagePID -> Message -> Process (Maybe Nat)
	Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)


run : Process t -> IO t 
run (Action x) = x
run (Pure x) = pure x 
run (x >>= f) = run x >>= (\x => run $ f x)
run (Spawn p) = do	
	Just pid <- spawn (run p)
		| Nothing => pure Nothing
	pure $ Just $ MkMessage pid
run (Request (MkMessage pid) msg) = do
	Just chan <- connect pid
		| _ => pure Nothing
	True <- unsafeSend chan msg
		| _ => pure Nothing 
	Just x <- unsafeRecv Nat chan 
		| _ => pure Nothing
	pure $ Just x
run (Respond f) = do 
	Just sender <- listen 1
		| Nothing => pure Nothing 
	Just msg <- unsafeRecv Message sender
		| Nothing => pure Nothing
	res <- run (f msg)
	unsafeSend sender res 
	pure $ Just msg

procAdder : Process () 
procAdder = do 
	Respond $ \msg => case msg of Add x y => Pure $ x + y
	procAdder

procMain : Process () 
procMain = do 
	Just adder_id <- Spawn procAdder 
		| Nothing => Action (putStrLn "Spawn failed")
	Just answer <- Request adder_id (Add 2 3)
		| Nothing => Action (putStrLn "Request failed")
	Action (printLn answer)



adder : IO ()
adder = do
	Just sender_chan <- listen 1
		| Nothing => adder
	Just msg <- unsafeRecv Message sender_chan
		| Nothing => adder
	case msg of 
		Add x y => do 
			ok <- unsafeSend sender_chan (x + y)
			adder

main : IO ()
main = do 
	Just adder_id <- spawn adder 
		| Nothing => putStrLn "Spawn failed"
	Just chan <- connect adder_id 
		| Nothing => putStrLn "Connection failed"
	ok <- unsafeSend chan (Add 2 3)
	Just answer <- unsafeRecv Nat chan 
		| Nothing => putStrLn "Send failed"
	putStrLn $ show answer




