-- This consists of the extracted code from the file Coqinsertionsort.v
-- Except to add deriving statements and declare axioms as types.

module VerifiedSort where

import qualified Prelude


data List a =
   Nil
 | Cons a (List a)
 deriving (Prelude.Show)

data Sumbool =
   Left
 | Right
 deriving (Prelude.Show)

-- AXIOM TO BE REALIZED. 
type A = Prelude.Int
  
-- Needed to implement this function
leq_dec :: A -> A -> Sumbool
leq_dec l r=
  if l Prelude.<= r then Left else Right

insert :: A -> (List A) -> List A
insert i l =
  case l of {
   Nil -> Cons i Nil;
   Cons x xs ->
    case leq_dec i x of {
     Left -> Cons i (Cons x xs);
     Right -> Cons x (insert i xs)}}

sort :: (List A) -> List A
sort l =
  case l of {
   Nil -> Nil;
   Cons x xs -> insert x (sort xs)}