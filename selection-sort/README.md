# Selection Sort

Proof that selection sort sorts (i.e. it **sorts** and the final vector is a **permutation** of initial one) written in Idris. Based mostly on chapter 9 from [Type Driven Development with Idris](https://www.manning.com/books/type-driven-development-with-idris) by Edwin Brady.

# Main types

### BOE 
``` haskell
data BOE : Nat -> Nat -> Type where
  B0 : BOE v Z
  BT : BOE k v -> BOE (S k) (S v)
```
BOE a b (Bigger Or Equal) means a >= b 

### Sorted
``` haskell
data Sorted : (v : Vect n Nat) -> Type where
  Sor0 : Sorted []
  Sor1 : Sorted [x]
  SorR : Sorted (x :: xs) -> BOE y x -> Sorted (y :: x :: xs)
````
Predicate that Vect is sorted. (Yes, it is sorted from biggest to smallest)

### VectIndex
``` haskell
data VectIndex : (a : Vect n t) -> (x : Nat) -> Type where
  BHere : VectIndex a Z
  BThere : VectIndex a n -> VectIndex (x :: a) (S n)
 ```
 Very similar to [Elem](https://github.com/idris-lang/Idris-dev/blob/master/libs/base/Data/Vect.idr#L599) but with Nat as an index. Used for WithoutOne.
 
### WithoutOne 
``` haskell
data WithoutOne : (a : Vect n t) -> (b : Vect (S n) t) -> (x : t) -> (vi : VectIndex a i) -> Type where
  WHere : WithoutOne xs (x :: xs) x BHere
  WThere : WithoutOne a b y vi -> WithoutOne (x :: a) (x :: b) y (BThere vi)
```
Predicate that shows that vector *a* is vector *b* without *x* on index *vi*. Predicate used for proving that removing element from a vect actually removes element.

### Subset 
``` haskell
data Subset : (a : Vect i Nat) -> (b : Vect j Nat) -> Type where
  SB0 : Subset [] b
  SBR : (el : Elem x b) -> Subset a b -> Subset (x :: a) b
 ```
Predicate that shows that vector a is a subset of a vector b.

### Permutation 
``` haskell
data Permutation : (a : Vect i Nat) -> (b : Vect i Nat) -> Type where
  Per : Subset a b -> Subset b a -> Permutation a b
```
Predicate that showss that a is a permutation of b. 

# Main function
``` haskell
selectionSort : (a : Vect n Nat) -> (v : Vect n Nat ** (Permutation v a, Sorted v))
```
Type definition says it all. Defining such function proves that *v* is **sorted** and *v* is a **permutation** of *a*.