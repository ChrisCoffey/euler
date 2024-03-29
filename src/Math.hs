{-# LANGUAGE MagicHash #-}
module Math where

import Control.Monad.State.Lazy (State, evalState, gets, modify)
import qualified Data.Set as Set
import qualified Data.Map as M
import qualified Data.IntMap as IM
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

-- Computes the number of digits to arbitrary precision in a square root
sqrtDigits :: Int -> Int -> ([Integer], [Integer])
sqrtDigits steps n = splitToParts $ calcDigit steps nDigits 0 0
  where
    integerDigits = length nDigits
    -- Pair up digits, starting from the right hand side
    nDigits = let
      digs = digits $ fromIntegral n
      in if even $ length digs
         then pairs digs
         else pairs (0:digs)

    calcDigit 0 [] _ p = p
    calcDigit _ [] 0 p = p
    calcDigit n [] c p = calcDigit n [(0, 0)] c p
    calcDigit digitsRemaining ((a,b):rest) c p = let
      aB = (a * 10) + b
      c' = (c * 100) + aB
      x = maximum [x' | x' <- [0..9], x' *((20 * p) + x') <= c']
      y = x * ((20 * p) + x)
      in calcDigit (digitsRemaining - 1) rest (c' - y) ((p * 10) + x)

    splitToParts root = let
      digs = digits root
      integerPart = take integerDigits digs
      decimalPart = drop integerDigits digs
      in (integerPart, decimalPart)



pairs :: [a] -> [(a,a)]
pairs [] = []
pairs [_] = []
pairs (a:b:rest) = (a,b): pairs rest


-- | Returns  the cyclic portion of a continued fraction
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

-- | Find progressively better and better rational approximations of a number's sqrt
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
factors = allFactors True True

properFactors :: Integer -> [Integer]
properFactors = (1:) . allFactors True False

allFactors :: Bool -> Bool -> Integer -> [Integer]
allFactors _ _ 1 =  [1]
allFactors onlyUnique includeN n =
  foldr (\(a,b) xs -> if (a == b && onlyUnique) then a:xs else a:b:xs ) (if includeN then [1,n] else []) rawFactors
  where
      rawFactors = [ (x, n `div` x) |
        let integerComponentSqrt = numerator . head $ convergents n,
        x <- [2..integerComponentSqrt],
        n `mod` x == 0
        ]

primeFactors :: Integer -> [Integer]
primeFactors = filter (Primes.trialDivisionPrimality . fromIntegral) . factors

-- All factorizations excluding (1,x)
factorTree :: Integer -> [[Integer]]
factorTree 1 = []
factorTree x
  | Primes.trialDivisionPrimality (fromIntegral x) = []
  | otherwise = unique . map sort . concatMap expandPair $ factorPairs facs
  where
    -- Produces a list of [small_1, big_1, small_2, big_2, ...]
    -- This list is always of an even length
    facs = allFactors False False x

    factorPairs [] = []
    factorPairs (s:b:rest) = (s,b) : factorPairs rest

    -- the pair (s,b) multiply together to equal x. This means the factor tree for (s,b) is
    -- [[s,b], (s:)<$>factorTree b, (b:)<$>factorTree s]
    expandPair :: (Integer, Integer) -> [[Integer]]
    expandPair (s,b) = [s,b] : ( (s:) <$> factorTree b) <> ((b:) <$> factorTree s)

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

-- The dropWhile is a dirty hack because I'm not in the mood to debug this function, nor
-- do I need to right now
digits :: Integer -> [Integer]
digits n = dropWhile (== 0) . snd $ foldl' (\(n', acc) _ -> step acc n') (n,[]) [1..numDigits]
  where
    numDigits = let
      a = ceiling $ logBase 10 ( fromIntegral n)
      in if n `mod` 10 == 0
         then a +1
         else a
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


extendPythagTrip :: Int -> (Int, Int, Int) -> [(Int, Int, Int)]
extendPythagTrip cap trip@(a,b,c) = [(x*a, x*b, x*c)  | x <- [1..cap]]

-- | Dynamic programming approach to finding the number of partitions for each value less than cap
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
    vals = zip generalPentagonalNumbers [0..]

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
      pN <- max 0 . sum <$> traverse (\(gK, k) -> (* (sign $ abs k)) <$> getP (n - gK) ) pents
      modify (M.insert n pN)
      pure pN

differences :: Num a => [a] -> [a]
differences xs = (\(l,r) -> r - l) <$> zip xs (tail xs)

-- | Newton's nth root formula provides successively better estimates of the root.
-- I've capped it at 100 itterations
nthRoot :: Int -> Integer -> Double
nthRoot n num = last . take 20 $ iterate (\x -> (cb * x) +(cc / (x ** ca))) 5
  where
    ca = fromIntegral n -1
    cb = ca / fromIntegral n
    cc = fromIntegral num / fromIntegral n

probablyIntegral :: RealFrac a => a -> Bool
probablyIntegral x = let
    up = ceiling x :: Int
    down = floor x :: Int
  in abs (fromIntegral up - x) <= 0.0001 || abs (fromIntegral down-x) <= 0.0001

perfectSquares :: [Integer]
perfectSquares = (^2) <$> [1..]

groupByLength :: [Integer] -> IM.IntMap [Integer]
groupByLength = foldl' (\m n -> IM.insertWith (<>) (floor . logBase 10 $ fromIntegral n) [n] m) IM.empty


approxNumDigits :: Int -> Int -> Float
approxNumDigits base exp = (logBase 10 $ fromIntegral base) * fromIntegral exp
