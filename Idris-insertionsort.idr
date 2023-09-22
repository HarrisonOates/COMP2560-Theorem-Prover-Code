-- Proof of correctness of insertion sort.
-- Compiles with idris2 --total
-- Author: Geun Yun

module InsertionSort

import Data.So
import Data.Vect

--------------------------------------------------------------------------------
-- Utility

-- Makes a best effort to return an error message.
-- Use this only on code paths that you can deduce should be unreachable. 
unsafeError : String -> unreachable
unsafeError message = believe_me message

--------------------------------------------------------------------------------
-- IsLte

-- Proof that `x <= y`.
IsLte : Ord e => (x:e) -> (y:e) -> Type
IsLte x y = So (x <= y)

-- Given an `x` and a `y`, returns a proof that either `x <= y` or `y <= x`.
chooseLte :
    Ord e => 
    (x:e) -> (y:e) -> 
    Either (IsLte x y) (IsLte y x)
chooseLte x y =
    case choose (x <= y) of 
        Left proofXLteY =>
            Left proofXLteY
        Right proofNotXLteY =>
            -- Given: not (x <= y)
            -- Derive: x > y
            -- Derive: y < x
            -- Derive: y <= x
            --
            -- Unfortunately Ord doesn't guarantee the preceding
            -- even though any sane implementation will conform
            -- to those rules. 
            case choose (y <= x) of 
                Left proofYLteX =>
                    Right proofYLteX
                Right proofNotYLteX =>
                    unsafeError ("Impossible with a sane Ord implementation, " ++
                    "since this is the y > x case which is already covered in line 36")

--------------------------------------------------------------------------------
-- IsSorted

-- Proof that `xs` is sorted.
data IsSorted : (xs:Vect n e) -> Type where
    IsSortedZero :
        IsSorted Nil
    IsSortedOne  :
        Ord e =>
        (x:e) ->
        IsSorted (x::Nil)
    IsSortedMany :
        Ord e => 
        (x:e) -> (y:e) -> (ys:Vect n'' e) ->    -- (n'' == (n - 2))
        (IsLte x y) -> IsSorted (y::ys) ->
        IsSorted (x::(y::ys))

--------------------------------------------------------------------------------
-- ElemsAreSame

-- Proof that set `xs` and set `ys` contain the same elements.
data ElemsAreSame : (xs:Vect n e) -> (ys:Vect n e) -> Type where
    NilIsNil : 
        ElemsAreSame Nil Nil
    PrependXIsPrependX :
        (x:e) -> ElemsAreSame zs zs' ->
        ElemsAreSame (x::zs) (x::zs')
    PrependXYIsPrependYX :
        (x:e) -> (y:e) -> ElemsAreSame zs zs' ->
        ElemsAreSame (x::(y::zs)) (y::(x::(zs'))
    SamenessIsTransitive :
        ElemsAreSame xs zs -> ElemsAreSame zs ys ->
        ElemsAreSame xs ys

XsIsXs : (xs:Vect n e) -> ElemsAreSame xs xs
XsIsXs Nil =
    NilIsNil
XsIsXs (x::ys) =
    PrependXIsPrependX x (XsIsXs ys)

-- NOTE: Needed to explicitly pull out the {x}, {y}, {zs}, {us} implicit parameters.
swapFirstAndSecondOfLeft : {x : e} -> {y : e} -> {zs : Vect n' e} -> {us : Vect (S (S n')) e} -> 
                           ElemsAreSame (x::(y::zs)) us -> ElemsAreSame (y::(x::zs)) us
swapFirstAndSecondOfLeft {x} {y} {zs} {us} proofXYZsIsUs =
    let proofYXZsIsXYZs = PrependXYIsPrependYX y x (XsIsXs zs) in
    let proofYZZsIsUs = SamenessIsTransitive proofYXZsIsXYZs proofXYZsIsUs in
    proofYZZsIsUs

--------------------------------------------------------------------------------
-- HeadIs, HeadIsEither

-- Proof that the specified vector has the specified head.
data HeadIs : Vect n e -> e -> Type where
    MkHeadIs : HeadIs (x::xs) x

-- Proof that the specified vector has one of the two specified heads.
-- 
-- NOTE: Could implement this as an `Either (HeadIs xs x) (HeadIs xs y)`,
--       but an explicit formulation feels cleaner.
data HeadIsEither : Vect n e -> (x:e) -> (y:e) -> Type where
    HeadIsLeft  : HeadIsEither (x::xs) x y
    HeadIsRight : HeadIsEither (x::xs) y x

--------------------------------------------------------------------------------
-- Insertion Sort

-- Inserts an element into a non-empty sorted vector, returning a new
-- sorted vector containing the new element plus the original elements.
insert' :
    (xs:Vect (S n) e) -> (y:e) -> (IsSorted xs) -> (HeadIs xs x) ->
    (xs':(Vect (S (S n)) e) ** ((IsSorted xs'), (HeadIsEither xs' x y), (ElemsAreSame (y::xs) xs')))
insert' (x::Nil) y (IsSortedOne x) MkHeadIs =
    case (chooseLte x y) of              
        Left proofXLteY =>
            let yXNilSameXYNil = PrependXYIsPrependYX y x (XsIsXs Nil) in
            (x::(y::Nil) **
             (IsSortedMany x y Nil proofXLteY (IsSortedOne y),
              HeadIsLeft,
              yXNilSameXYNil))
        Right proofYLteX =>
            let yXNilSameYXNil = XsIsXs (y::(x::Nil)) in
            (y::(x::Nil) ** 
             (IsSortedMany y x Nil proofYLteX (IsSortedOne x),
              HeadIsRight,
              yXNilSameYXNil))
insert' (x::(y::ys)) z proofXYYsIsSorted MkHeadIs =
    case proofXYYsIsSorted of
        (IsSortedMany x y ys proofXLteY proofYYsIsSorted) =>
            case (chooseLte x z) of
                Left proofXLteZ =>
                    -- x::(insert' (y::ys) z)
                    let proofHeadYYsIsY = the (HeadIs (y::ys) y) MkHeadIs in
                    case (insert' (y::ys) z proofYYsIsSorted proofHeadYYsIsY) of
                        -- rest == (_::tailOfRest)
                        ((y::tailOfRest) ** (proofRestIsSorted, HeadIsLeft, proofZYYsSameRest)) =>
                            let proofXZYYsIsXRest = PrependXIsPrependX x proofZYYsSameRest in
                            let proofZXYYsIsXRest = swapFirstAndSecondOfLeft proofXZYYsIsXRest in
                            (x::(y::tailOfRest) **
                             (IsSortedMany x y tailOfRest proofXLteY proofRestIsSorted,
                              HeadIsLeft,
                              proofZXYYsIsXRest))
                        ((z::tailOfRest) ** (proofRestIsSorted, HeadIsRight, proofZYYsSameRest)) =>
                            let proofXZYYsIsXRest = PrependXIsPrependX x proofZYYsSameRest in
                            let proofZXYYsIsXRest = swapFirstAndSecondOfLeft proofXZYYsIsXRest in
                            (x::(z::tailOfRest) **
                             (IsSortedMany x z tailOfRest proofXLteZ proofRestIsSorted,
                              HeadIsLeft,
                              proofZXYYsIsXRest))
                Right proofZLteX =>
                    -- z::(x::(y::ys))
                    let proofZXYYsIsZXYYs = XsIsXs (z::(x::(y::ys))) in
                    (z::(x::(y::ys)) **
                     (IsSortedMany z x (y::ys) proofZLteX proofXYYsIsSorted,
                      HeadIsRight,
                      proofZXYYsIsZXYYs))

-- Inserts an element into a sorted vector, returning a new
-- sorted vector containing the new element plus the original elements.
insert :
    Ord e =>
    (xs:Vect n e) -> (y:e) -> (IsSorted xs) -> 
    (xs':(Vect (S n) e) ** ((IsSorted xs'), (ElemsAreSame (y::xs) xs')))
insert Nil y IsSortedZero =
    ([y] ** (IsSortedOne y, XsIsXs [y]))
insert (x::xs) y proofXXsIsSorted =
    let proofHeadOfXXsIsX = the (HeadIs (x::xs) x) MkHeadIs in
    case (insert' (x::xs) y proofXXsIsSorted proofHeadOfXXsIsX) of
        (xs' ** (proofXsNewIsSorted, proofHeadXsNewIsXOrY, proofYXXsIsXsNew)) =>
            (xs' ** (proofXsNewIsSorted, proofYXXsIsXsNew))

-- Sorts the specified vector,
-- returning a new sorted vector with the same elements.
insertionSort :
    Ord e =>
    (xs:Vect n e) ->
    (xs':Vect n e ** (IsSorted xs', ElemsAreSame xs xs'))
insertionSort Nil =
    (Nil ** (IsSortedZero, NilIsNil))
insertionSort (x::ys) =
    case (insertionSort ys) of
        (ysNew ** (proofYsNewIsSorted, proofYsIsYsNew)) =>
            case (insert ysNew x proofYsNewIsSorted) of
                (result ** (proofResultIsSorted, proofXYsNewIsResult)) =>
                    let proofXYsIsXYsNew = PrependXIsPrependX x proofYsIsYsNew in
                    let proofXYsIsResult = SamenessIsTransitive proofXYsIsXYsNew proofXYsNewIsResult in
                    (result ** (proofResultIsSorted, proofXYsIsResult))