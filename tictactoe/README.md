# Tic Tac Toe

Simple tic tac toe written in Idris. Based mostly on chapter 12 from [Type Driven Development with Idris](https://www.manning.com/books/type-driven-development-with-idris) by Edwin Brady.

# Board

Board is represented as 3x3 matrix with Maybe Field fields (where Field is Cross or Circle). Matrix is implemented as Vect n (Vect m a). For accessing fields in a matrix I used FinDouble which is just a pair of [Fins](https://github.com/idris-lang/Idris-dev/blob/master/libs/base/Data/Fin.idr). 
