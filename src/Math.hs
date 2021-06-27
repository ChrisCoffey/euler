{-# LANGUAGE MagicHash #-}
module Math where

import Control.Monad.State.Lazy (State, evalState, gets, modify)
import qualified Data.Set as Set
import qualified Data.Map as M
import Data.List (sort, sortBy, group)
import Data.Foldable (foldl')
import Data.Ratio
import Data.Ord (comparing)
import GHC.Integer.Logarithms
import GHC.Exts
import Debug.Trace

import Primes

-- Produce the in-order "choose" selections from a list
choose ::
  Int
  -> [a]
  -> [[a]]
choose _ [] = []
choose 0 _ = []
choose 1 ls =  (\x -> [x]) <$> ls
choose n ls@(a:rest)
  | n >= length ls = [ls]
  | otherwise = (fmap ((:) a) $ choose (n-1) rest) <> choose n rest

chooseWithReplacement :: Int -> [a] -> [[a]]
chooseWithReplacement _ [] = []
chooseWithReplacement 0 _ = []
chooseWithReplacement 1 ls = (: []) <$> ls
chooseWithReplacement num ls
  | num >= length ls = [ls]
  | otherwise = foldl (\xs _ -> concatMap (\ys -> (:ys) <$> ls )xs) (chooseWithReplacement 1 ls) [1..num-1]

cartesianProduct ::
  [a] ->
  [a] ->
  [[a]]
cartesianProduct as bs = [ [b,a] | a <- as, b <- bs]

-- Replaces the specified indexes with 'newVal'
-- The list is zero indexed
replaceAt ::
  [Int]
  -> a
  -> [a]
  -> [a]
replaceAt indices newVal ls =
  go 0 indices ls
  where
    go _ [] ls = ls
    go _ _ [] = []
    go n (i:ixs) (a:rest)
      | n == i = newVal : go (n+1) ixs rest
      | otherwise = a : go (n+1) (i:ixs) rest

-- Find the indexes where 'toFind' occurs
indexesFor :: (Eq a) =>
  [a]
  -> a
  -> [Int]
indexesFor ls toFind =
  map snd . filter ((== toFind) . fst) $ zip ls [0..]

-- Returns a list of all values occuring more than once
duplicates :: (Eq a, Ord a) =>
  [a]
  -> [a]
duplicates = map head . filter ((>= 2) . length). group . sort

unique :: (Eq a, Ord a) =>
  [a]
  -> [a]
unique = Set.toList . Set.fromList

intLog10 :: Integer -> Int
intLog10 n = I# (integerLogBase# 10 n)
-- The I# boxes the returned unboxed integer
-- This requires the MagicHash extension to work properly, otherwise # is interpreted as a variable

-- concatenate two numbers to create a third. Beware of overflow for bounded types
concatNumbers :: Integral a => a -> a -> a
concatNumbers l r = (l * (10 ^ (intLog10 (fromIntegral r) + 1))) + r


triangleNumbers :: [Int]
triangleNumbers = (\x -> (x * (x+1)) `div` 2) <$> [1..]

squareNumbers :: [Int]
squareNumbers = (\x -> x * x) <$> [1..]

pentagonalNumbers :: [Int]
pentagonalNumbers = (\x -> (x * (3 * x - 1)) `div` 2) <$> [1..]

generalPentagonalNumbers :: [Integer]
generalPentagonalNumbers = concatMap (\x -> [f x, f (-x)]) [1..]
  where
    f x = (x * (3 * x - 1)) `div` 2

hexagonalNumbers :: [Int]
hexagonalNumbers = (\x -> x * (2 * x - 1) ) <$> [1..]

heptagonalNumbers :: [Int]
heptagonalNumbers = (\x -> x * (5 * x - 3) `div` 2 ) <$> [1..]

octagonalNumbers :: [Int]
octagonalNumbers = (\x -> x * (3 * x - 2) ) <$> [1..]

cubes :: [Int]
cubes = [ x*x*x | x <- [1..]]

numDigits :: Integer -> Integer -> Integer
numDigits l r = (+ 1) . floor $ (logBase 10 $ fromIntegral l) + (logBase 10 $ fromIntegral r)

isPerfectSquare :: Int -> Bool
isPerfectSquare x = let
  a = floor . sqrt $ fromIntegral x
  in a * a == x

sqrtContinuedFraction :: Int -> [Integer]
sqrtContinuedFraction n
  | isPerfectSquare n = [r]
  | otherwise = go r 0 1
  where
    r :: Integer
    r = floor . sqrt $ fromIntegral n

    go :: Integer -> Integer -> Integer -> [Integer]
    go a p q = let
      p' = a*q - p
      q' = (fromIntegral n - p'* p') `div` q
      a' = (r+p') `div` q'
      in if q' /= 1
         then a' : go a' p' q'
         else [a']

convergents :: Integer -> [Rational]
convergents n
  | isPerfectSquare (fromIntegral n) = [r % 1]
  | otherwise = let
    (a:rest) = cycle . sqrtContinuedFraction $ fromIntegral n
    c'' = r % 1
    c' = (r*a + 1)% a
    in c'':c':go rest c'' c'

  where
    r :: Integer
    r = floor . sqrt $ fromIntegral n

    go (a:rest) c'' c' = let
      num = (a * numerator c') + numerator c''
      den = (a * denominator c') + denominator c''
      c = num % den
      in c : go rest c' c

factors :: Integer -> [Integer]
factors 1 = [1]
factors n =
  foldr (\(a,b) xs -> if a == b then a:xs else a:b:xs ) [1,n] rawFactors
  where
      rawFactors = [ (x, n `div` x) |
        let integerComponentSqrt = numerator . head $ convergents n,
        x <- [2..integerComponentSqrt],
        n `mod` x == 0
        ]

primeFactors :: Integer -> [Integer]
primeFactors = filter (Primes.trialDivisionPrimality . fromIntegral) . factors

binaryGCD :: Integer -> Integer -> Integer
binaryGCD a b
  | a == b = a
  | a == 0 = b
  | b == 0 = a
  | odd a && even b = binaryGCD a (b `div` 2)
  | odd a && a > b = binaryGCD ((a-b) `div` 2) b
  | odd a = binaryGCD ((b-a) `div` 2) a
  | otherwise = if odd b
                then binaryGCD (a`div`2) b
                else binaryGCD (a`div`2) (b `div` 2)

-- The number of numbers < n that are relatively prime to n
totient :: Integer -> Integer
totient n = floor $ foldl (*) (fromIntegral n) [1 - (1 % fromIntegral  x) | x <- factors n, cryptoPrimeCheck x]
  -- fromIntegral . length $ [x | x <- [1..(n-1)], gcd x n == 1]
  -- ^ This is a correct definition, but very slow and inelegant

-- A sieve for calculating totients
totients :: Integer -> [Integer]
totients cap = map snd . sortBy (comparing fst) . M.toList $ foldl' step idx [2..cap]
  where
    idx = M.fromList [(x, x)| x <- [2..cap]]
    step index d = let
      val = index M.! d
      in if val == d
         then foldl' (innerStep d) index [d,d*2 .. cap]
         else index

    innerStep d index e = let
      val = index M.! e
      in M.insert e ((val `div` d) * (d-1)) index

properFractions = [ n % d |
  d <- [2..],
  n <- [1..d-1],
  gcd n d == 1
  ]

reducedProperFrac n d = gcd n d == 1 && n < d

digits :: Integer -> [Integer]
digits n = snd $ foldl' (\(n', acc) _ -> step acc n') (n,[]) [1..numDigits]
  where
    numDigits = ceiling $ logBase 10 ( fromIntegral n)
    step ls n' = let
      digit = n' `mod` 10
      in (n' `div` 10, digit:ls)

factorialChain :: Int -> [Int]
factorialChain n = n : go (Set.fromList [n]) n
  where
    factorial x = product [1..x]
    go :: Set.Set Int -> Int -> [Int]
    go seen n' = let
      facSum = fromIntegral . sum $ factorial <$> digits (fromIntegral n')
      seen' = Set.insert facSum seen
      in if facSum `Set.member` seen
         then []
         else facSum : go seen' facSum

-- Produce all of the primative pythagorean triplets (triplets for which the values do not share a common factor),
-- as well as some of their multiples
basePythagoreanTriplets :: Int ->  [(Int, Int, Int)]
basePythagoreanTriplets cap = [ (a,b,c) |
  m <- [2..cap],
  n <- [1..m-1],
  let a = (m^2 - n^2),
  let b = (2 * m * n),
  let c = (m^2 + n^2)
  ]

partitions :: Integer -> [(Integer, Integer)]
partitions cap = evalState (traverse (\n -> (\ways -> (n, ways)) <$> waysToMake n (n-1)) [1..cap]) M.empty
  where
    waysToMake :: Integer -> Integer -> State (M.Map (Integer, Integer) Integer) Integer
    waysToMake n m
      | m == 0 = pure 0
      | n == 0 = pure 1
      | n < 0 = pure 0
      | otherwise = do
          knownM <- gets (M.lookup (n,m)) -- This is indexed on n & m because each value of m may be unique to a given n, but can be reused
          case knownM of
            Just ways ->
              pure ways
            Nothing -> do
              waysA <- waysToMake n (m - 1) -- Take the same n, but the next step down for m. This is
              waysB <- waysToMake (n - m) m
              let ways = waysA + waysB
              modify (M.insert (n, m) ways)
              pure ways

data EulerMemo = EM {
  cCache :: M.Map Integer Integer,
  kCache :: M.Map Integer Integer
  }

partitionsEuler :: [Integer] -> [(Integer, Integer)]
partitionsEuler ls = zip [1..] $ evalState (traverse k ls) initialCaches
  where
    initialCaches = EM M.empty M.empty

    c :: Integer -> State EulerMemo Integer
    c n = do
      known <- gets (M.lookup n . cCache)
      case known of
        Just x -> pure x
        Nothing -> do
          let x = sum (factors n)
          modify (\m -> m {cCache = M.insert n x (cCache m)})
          pure x

    k :: Integer -> State EulerMemo Integer
    k 1 = pure 1
    k n = do
      known <- gets (M.lookup n . kCache)
      case known of
        Just ways -> pure ways
        Nothing -> do
          partialWays <- traverse (step n) [1..n-1]
          facs <- c n
          let ways = (facs + sum partialWays) `div` n
          modify (\m -> m {kCache = M.insert n ways (kCache m)})
          pure ways

    step n j = do
      a <- k (n-j)
      b <- c j
      pure (a * b)

-- This generates partition counts using Euler's pentagonal number theory. The
-- theory provides a recurrence for calculating partitions, which means p(n+1) isNaN
-- p(n) + <next term>. That has an exponential increase in performance relative to
-- my dynamic programming approaches above
partitionsPentagonal :: [(Integer, Integer)]
partitionsPentagonal = zip [1..] $ evalState (traverse countPartitions [1..]) M.empty
  where
    vals = zip generalPentagonalNumbers $ concatMap (\x -> [x, -x]) [1..]

    sign :: Integer -> Integer
    sign k
      | k `mod` 4 > 1 = -1
      | otherwise = 1

    getP :: Integer -> State (M.Map Integer Integer) Integer
    getP n
      | n == 0 = pure 1
      | n < 0 = pure 0
      | otherwise = gets (M.! n)

    countPartitions :: Integer -> State (M.Map Integer Integer) Integer
    countPartitions n = do
      let pents = takeWhile ((<= n) . fst) vals
      pN <- sum <$> traverse (\(gK, k) -> (* (sign $ abs k)) <$> getP (n - gK) ) pents
      modify (M.insert n pN)
      pure pN

