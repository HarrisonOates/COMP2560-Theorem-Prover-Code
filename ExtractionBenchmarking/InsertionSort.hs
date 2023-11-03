module InsertionSort where

import qualified Prelude

insert :: Prelude.Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) = if x Prelude.<= y then x:y:ys else y:(insert x ys)

sort :: Prelude.Ord a => [a] -> [a]
sort [] = []
sort (x:xs) = insert x (sort xs)