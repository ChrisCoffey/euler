module Primes
(
  primes,
  trialDivisionPrimality,
  primesLessThanTenMM,
  bunchOfPrimes,
  cryptoPrimeCheck
)
where

import Data.IORef
import GHC.IO
import Data.Array.Unboxed
import Crypto.Number.Prime

primesLessThanTenMM :: [Int]
primesLessThanTenMM = unsafePerformIO $ readIORef _primesLessThanTenMM

_primesLessThanTenMM :: IORef [Int]
_primesLessThanTenMM = unsafePerformIO $ newIORef $ takeWhile (< 10000000) bunchOfPrimes

bunchOfPrimes :: [Int]
bunchOfPrimes = 2 : oddprimes ()
  where
    oddprimes = (3 :) . sieve 3 [] . oddprimes
    sieve x fs (p:ps) = [i*2 + x | (i,True) <- assocs a]
                        ++ sieve (p*p) ((p,0) :
                             [(s, rem (y-q) s) | (s,y) <- fs]) ps
      where
      q = (p*p-x)`div`2
      a :: UArray Int Bool
      a = accumArray (\ b c -> False) True (1,q-1)
                     [(i,()) | (s,y) <- fs, i <- [y+s, y+s+s..q]]

-- This isn't memoized across function calls
-- Introduce a version that's stored in an IORef
primes :: Integral a => [a]
primes = 2:3:5: minus primeWheel (foldr (\p r-> p*p : union [p*p+p, p*p+2*p..] r) [] primes)
-- 2 : minus [3..] (foldr (\p r-> p*p : union [p*p+p, p*p+2*p..] r) [] primes)

primeWheel :: Integral a => [a]
primeWheel = 7:11:13:17:19:23:29:31: turn [7, 11, 13, 17, 19, 23, 29, 31]
  where
    turn xs = let
      ys = (+ 30) <$> xs
      [a', b', c', d', e', f', g', h'] = ys
      in a':b':c':d':e':f':g':h': turn ys

cryptoPrimeCheck :: Integral a => a -> Bool
cryptoPrimeCheck = isProbablyPrime . fromIntegral

-- The majority of numbers are divisible by a small prime
trialDivisionPrimality :: Int -> Bool
trialDivisionPrimality n
  | n `mod` 2 == 0 || n `mod` 3 == 0 = False
  | otherwise =  let
    top = floor $ sqrt (fromIntegral n)
    in not $ shortAny (\odd -> n `mod` odd == 0) [5,7..top]

shortAny :: (a -> Bool) -> [a] -> Bool
shortAny f [] = False
shortAny f (x:rest) = f x || shortAny f rest

minus :: Ord a => [a] -> [a] -> [a]
minus (x:xs) (y:ys) =
    case compare x y of
        LT -> x: minus xs (y:ys)
        GT -> minus (x:xs) ys
        EQ -> minus xs ys
minus xs _ = xs --Covers the empty list case b/c it has already passed the pattern above

union :: Ord a => [a] -> [a] -> [a]
union (x:xs) (y:ys) =
    case compare x y of
        LT -> x: union xs (y:ys)
        GT -> y: union (x:xs) ys
        EQ -> x: union xs ys
union xs _ = xs
