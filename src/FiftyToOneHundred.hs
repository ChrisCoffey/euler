module FiftyToOneHundred where

import qualified Info.FiftyToOneHundred  as DATA
import EarlyProblems (maximumPathPyramid)
import EarlyProblems as Funcs
import qualified Primes
import qualified Data.Map as M
import Data.Foldable (foldl', find)
import Data.List (sort)
import Data.Maybe (mapMaybe, fromMaybe)

-- which prime, below one-million, can be written as the sum of the most consecutive primes?
--
-- A "range of prime sums" is defined as the sum of primes [p1..pn]
--
-- Brute force:
--  1) Compute all primes up to 1MM
--  2) Reverse the list of primes
--  3) for each  prime P, compute & subtract out prime ranges
--  4) Stop evaluating a prime once p1 in a given range is greater than (P - prime range sum)
--  5) If (P - prime range sum) == 0, record P & the length of prime range
--  6) Else advance the range start to the next prime & GOTO (3)
--  7) The prime P stored in the "Max range length" that remains after evaluating all primes is the answer
--
-- Efficient Algorithm:
-- Constantly recomputing ranges is very expensive. Instead, precompute the ranges & store them.
-- Take advantage of the property that primes can be processed in-order. This means that for prime ranges ending
-- at Pa and Pb - where Pb occurs somewhere after Pa - the length of the range between Pa -> Pb is
-- index(Pb) - index(Pa). For a prime P, assuming it is the sum of some prime range, the longest range can be found by
-- traversing the sums in descending order, subtracting P from range sum R (R-P), then checking whether R-P
-- is the sum of another prime range R'. If so, the length of the range is index(R) - index(R'). Check this for
problem50 :: Integer
problem50 =
  fst $ foldl largestRange (-1, 0) $ filter (> 900000) primesLessThanOneMM
  where
    probableMaxPrimeValue = 25000
    primesLessThanOneMM = takeWhile (< 1000000) Primes.primes
    primesLessThanProbableMax = filter (< probableMaxPrimeValue) primesLessThanOneMM

    primeRanges = funcOfRanges (+) primesLessThanProbableMax
    rangeList = M.toList primeRanges

    largestRange (currentMax, rangeLength) p = let
      match (k, kLen) =  (\len -> kLen - len ) <$> M.lookup (k - p) primeRanges
      matches = mapMaybe match rangeList
      in case matches of
        [] -> (currentMax, rangeLength)
        _ -> if maximum matches > rangeLength
             then (p, maximum matches)
             else (currentMax, rangeLength)

      -- Given the prime P, check all primes in the possible range for summations.


-- Find the smallest prime by which replacing part of the number with the same digit it creates
-- an eight prime value family.
--
-- They must all be the same length, b/c only swaps are allowed (no deletions or insertions)
-- The same index must be swapped in each number
--
-- It can be solved by iterating through each prime & swapping out each set of digits, but that has terrible
-- performance. Instead, try first
problem51 :: Integer
problem51 = 42


-- Find the smallest number where 1->6 xN all use the same digits
--
-- This could be a brute-force search via a sieving algorithm, but maybe there's
-- a more efficient way to address this problem.
problem52 :: Int
problem52 =
  fromMaybe 0 $ find sameDigitsRange [1..]
  where
    sameDigits l r =  ( sort  $ digits l ) == ( sort  $ digits r )
    sameDigitsRange l = all id $ (\i -> sameDigits l (l * i )) <$> [2..6]

-- How many values of N-choose-R for N <= 100 are greater than 1M?
-- This is pretty simple to compute thanks to Haskell's arbitrary sized integers, but not
-- very interesting.
--
-- Its possible to adapt the n choose r formula into a far more efficient constrction,
-- particularly if you're performing an exhaustive search like this problem demands. But,
-- binomial coefficients also form pascal's triangle, so by computing that it saves a whole
-- bunch of CPU cycles, at the cost of a slightly more complex algorithm
problem53 :: Int
problem53 =  length $ filter (> 1000000) [
  (factorial n) `div` ((factorial r) * factorial (n - r)) |
    n <- [1..100],
    r <- [1..n]
  ]

problem53' :: Int
problem53' = length $ filter (> 1000000) [
  nChoose n (r - 1) |
  n <- [1..100],
  r <- [1..n]
  ]
  where
    nChoose n 0 = n
    nChoose n i = ((n - i) / (i+1)) * nChoose n (i - 1)

problem67 :: Integer
problem67 = maximumPathPyramid DATA.problem67

funcOfRanges :: Ord a => (a -> a -> a) -> [a] -> M.Map a Int
funcOfRanges f range =
  M.fromList . foldl' accumulate [] $ zip range [1..]
  where
    accumulate [] a = [a]
    accumulate ((x, i):xs) (a, j) = (f a x, j) : (x, i) : xs

