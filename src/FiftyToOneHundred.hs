module FiftyToOneHundred where

import qualified Info.FiftyToOneHundred  as DATA
import EarlyProblems (maximumPathPyramid)
import EarlyProblems as Funcs
import qualified Data.Map as M
import Data.Foldable (foldl')
import Data.Maybe (mapMaybe)

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
    primesLessThanOneMM = takeWhile (< 1000000) Funcs.primes
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


problem67 :: Integer
problem67 = maximumPathPyramid DATA.problem67

funcOfRanges :: Ord a => (a -> a -> a) -> [a] -> M.Map a Int
funcOfRanges f range =
  M.fromList . foldl' accumulate [] $ zip range [1..]
  where
    accumulate [] a = [a]
    accumulate ((x, i):xs) (a, j) = (f a x, j) : (x, i) : xs

