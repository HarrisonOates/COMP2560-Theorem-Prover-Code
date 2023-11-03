-- This sets up the benchmarks for the extraction process.
-- To run, open GHCI and type :set +s, before comparing both.
module Benchmark where

    import qualified Prelude as P
    import VerifiedSort as V
    import InsertionSort as I 

    -- Convert a native list to the type that verified sort created
    listGen :: [A] -> List A 
    listGen [] = Nil
    listGen (x:xs) = Cons x (listGen xs)

    -- The test cases
    test1 = P.reverse [1..10000]
    test1' = listGen test1
    
    -- The benchmarks
    nativeSortBench1 = I.sort test1

    verifiedSortBench1 = V.sort test1'





    
