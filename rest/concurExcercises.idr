module Chapter15 

import System
import System.Concurrency.Channels

data Message = Add Int Int 

adder' : Channel -> IO () 
adder' sender_chan = do
	Just msg <- unsafeRecv Message sender_chan
		| Nothing => do 
			putStrLn " adder: Nothing from unsagfeRecv"
			adder' sender_chan
	putStrLn "adder: Just from unsafeRecv"
	case msg of 
		(Add x y) => do 
			True <- unsafeSend sender_chan (x + y)
				| _ => do
					putStrLn "adder: False from unsafeSend"
					adder' sender_chan
			putStrLn $ "adder : unsafeSend result = " ++ (show True)
			adder' sender_chan

adder : IO () 
adder = do 
	rc <- listen 10
	case rc of 
		Nothing => do
			putStrLn  "adder : Nothign from listen"
			adder
		(Just sender_chan) => do 
			putStrLn "adder: Just from listen"
			adder' sender_chan

main : IO () 
main = do 
	Just adder_id <- spawn adder
		| Nothing => do 
			putStrLn "main: Nothing from spawn"
			pure ()
	putStrLn "main: Just from spawn"
	Just chan <- connect adder_id
		| Nothing => do
			putStrLn "main: Nothing from connect"
			pure ()
	putStrLn "main: Just from connect"

	True <- unsafeSend chan (Add 1 2)
		| _ => do 
			putStrLn "main: False from unsafeSend"
			pure ()
	putStrLn $ "main: unsafeSend (Add 1 2) result =" ++ (show True)

	True <- unsafeSend chan (Add 2 3)
		| _ => do 
			putStrLn "main: False from unsafeSend"
			pure ()
	putStrLn $ "main: unsafeSend (Add 2 3) result =" ++ (show True)

	Just answer1 <- unsafeRecv Nat chan 
		| Nothing => do
			putStrLn "main: Nothing from unsafeRecv"
			pure ()

	Just answer2 <- unsafeRecv Nat chan 
		| Nothing => do
			putStrLn "main: Nothing from unsafeRecv"
			pure ()

	putStrLn "main: Just from unsafeRecv"
	putStrLn $ "main: answer1 = " ++ (show answer1)
	putStrLn $ "main: answer2 = " ++ (show answer2)
	pure ()

