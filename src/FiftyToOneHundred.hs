module FiftyToOneHundred where

import qualified Info.FiftyToOneHundred  as DATA
import EarlyProblems (maximumPathPyramid)
import EarlyProblems as Funcs
import qualified Primes
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable (foldl', find)
import Data.List (sort, sortOn, group, find, intersect)
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Bits
import Data.Char (ord, chr)
import Math

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
problem51 :: M.Map String [Integer]
problem51 =
  M.filter ((>= 8) . length) primeTable
  where
    primesLessThanOneMM = takeWhile (<= 1000000) primes

    primeTable = let
      f table (key, prime) = M.insertWith (<>) key [prime] table
      in foldl' f M.empty $ concatMap primeKeys $ interestingIndexes $ nontrivialPrimes primesLessThanOneMM

    -- This is duplicated work, but simpler to reason about as multiple passes
    nontrivialPrimes :: [Integer] -> [Integer]
    nontrivialPrimes = filter ( any ((>= 2) . length) . group . sort . show)

    -- Given a list of primes, this annotates them with the repeated digits, and the location where they occur
    interestingIndexes :: [Integer] -> [(Integer, [(Char, [Int])])]
    interestingIndexes = map (\rawPrime -> (\prime -> (rawPrime, map (\n -> (n, indexesFor prime n)) $ duplicates prime)) $ show rawPrime)

    indexPermutations :: [Int] -> [[Int]]
    indexPermutations ixs = concat [ choose n ixs | n <- [2..length ixs] ]

    primeKeys :: (Integer, [(Char, [Int])]) -> [(String, Integer)]
    primeKeys primeWithIndexes = let
      primeString = show $ fst primeWithIndexes
      indices = map snd $ snd primeWithIndexes
      allPrimeIndexGroups = concat $ indexPermutations <$> indices
      in map (\x -> (replaceAt x '*' primeString, fst primeWithIndexes)) allPrimeIndexGroups

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


data Face = Two | Three | Four | Five | Six | Seven | Eight | Nine | Ten | Jack | Queen | King | Ace
  deriving (Eq, Ord, Enum, Show)

data Suit = Heart | Club | Spade | Diamond deriving (Eq, Show)

data Card = Card {face :: Face, suit :: Suit} deriving (Show)

data Score
  = High Face
  | Pair Face
  | TwoPair Face Face
  | Triple Face
  | Straight Face
  | Flush
  | FullHouse {triple :: Face, double :: Face}
  | FourOfKind Face
  | StraightFlush Face Suit
  | RoyalFlush
  deriving (Show, Eq)

-- This relies on the fall-through matching behavior for different cases
-- The scored hands are listed in ascending score order, allowing in-order comps
instance Ord Score where
  compare (High l) (High r) = compare l r
  compare (High _) _ = LT
  compare _ (High _) = GT

  compare (Pair l) (Pair r) = compare l r
  compare (Pair _) _ = LT
  compare _ (Pair _) = GT

  compare (TwoPair a b) (TwoPair x y)
    | a == x = compare b y
    | otherwise = compare a x
  compare (TwoPair a b) _ = LT
  compare _ (TwoPair a b) = GT

  compare (Triple l) (Triple r) = compare l r
  compare (Triple _) _ = LT
  compare _ (Triple _) = GT

  compare (Straight l) (Straight r) = compare l r
  compare (Straight _) _ = LT
  compare _ (Straight _) = GT

  compare Flush Flush = EQ
  compare Flush _ = LT
  compare _ Flush = GT

  compare (FullHouse tl dl) (FullHouse tr dr) = compare tl tr
  compare (FullHouse _ _) _ = LT
  compare _ (FullHouse _ _) = GT

  compare (FourOfKind l) (FourOfKind r) = compare l r
  compare (FourOfKind _) _ = LT
  compare _ (FourOfKind _) = GT

  compare (StraightFlush l _) (StraightFlush r _) = compare l r
  compare (StraightFlush _ _) _ = LT
  compare _ (StraightFlush _ _) = GT

  compare RoyalFlush RoyalFlush = EQ

newtype ScoredHand = ScoredHand (Score, [Card])
  deriving (Show)

-- Poker hand simulator
problem54 :: IO Int
problem54 = do
  rawLines <- lines <$> readFile dataFile
  let hands = map (parseHand . words) rawLines
      scored = map (\(p1, p2) -> (ScoredHand ((scoreHand p1), p1), ScoredHand ((scoreHand p2), p2))) hands
      forPlayerOne = filter playerOneWins scored
      numWins = length forPlayerOne
  -- putStrLn $ unlines $ show <$> filter draws scored
  pure numWins
  where
    dataFile = "src/Info/poker.txt"
    parseHand rawCards = ( toHand $ take 5 rawCards, toHand $ drop 5 rawCards)
    toHand = sortOn face . map parseCard
    parseCard [f,s] = Card {face = parseFace f, suit = parseSuit s}

    parseFace '2' = Two
    parseFace '3' = Three
    parseFace '4' = Four
    parseFace '5' = Five
    parseFace '6' = Six
    parseFace '7' = Seven
    parseFace '8' = Eight
    parseFace '9' = Nine
    parseFace 'T' = Ten
    parseFace 'J' = Jack
    parseFace 'Q' = Queen
    parseFace 'K' = King
    parseFace 'A' = Ace

    parseSuit 'H' = Heart
    parseSuit 'S' = Spade
    parseSuit 'C' = Club
    parseSuit 'D' = Diamond

    -- cards is a sorted (by face) collection of cards
    scoreHand cards@[c1, c2, c3, c4, c5]
      | isFlush cards && isStraight cards && face c1 == Ten = RoyalFlush
      | isFlush cards && isStraight cards = StraightFlush (face c1) (suit c1)
      | face c1 == face c4 || face c2 == face c5 = FourOfKind (face c2)
      | face c1 == face c2 && face c1 /= face c3 && face c3 == face c5 = FullHouse (face c3) (face c1)
      | face c1 == face c3 && face c1 /= face c4 && face c4 == face c5 = FullHouse (face c3) (face c4)
      | isFlush cards = Flush
      | isStraight cards = Straight (face c1)
      | face c1 == face c3 = Triple (face c1)
      | face c2 == face c4 = Triple (face c2)
      | face c3 == face c5 = Triple (face c3)
      | length (pairs cards) == 2 = let
        [low, high] = pairs cards
        in TwoPair high low
      | length (pairs cards) == 1 = let
        [pair] = pairs cards
        in Pair pair
      | otherwise = High (face c5)

    isFlush (c:rest) = all ((== suit c) . suit) rest
    isStraight :: [Card] -> Bool
    isStraight (c:rest) = snd $ foldl (\ (x, isSucc) c' -> (face c', isSucc && succ x == face c')) (face c, True) rest
    pairs = map head . filter ((== 2) . length) . group . map face

    playerOneWins (ScoredHand (p1Score, p1Cards), ScoredHand (p2Score, p2Cards))
      | p1Score == p2Score = compareHighCards (face <$> reverse p1Cards) (face <$> reverse p2Cards)
      | otherwise = p1Score > p2Score

    draws (ScoredHand (p1Score, _), ScoredHand (p2Score, _)) = p1Score < p2Score

    -- This fails if there isn't a clear winner in the hand
    compareHighCards (l:ls) (r:rs)
      | l == r = compareHighCards ls rs
      | otherwise = l > r

-- Determine the Lychrel numbers below 10k.
--
-- I'm approaching this as a dynamic programming problem, where each loop's Lychrel-ness is stored in
-- a map and checked before performing the ops. Although even then, because the check is capped at 50
-- iterations, this is only 500k steps
problem55 :: Int
problem55 = let
  lychrelCount = length . filter id $ map (checkPalindromeCycle 1) [1..10000::Integer]
  in lychrelCount
  where
    -- Initialize an array of boolean values
    -- Whenever a value is found to be Lychrel, increment the counter
    checkPalindromeCycle 50 x = not . palindromeNumber $ lychrelStep x
    checkPalindromeCycle iters x = let
      atStep = lychrelStep x
      in if palindromeNumber atStep then False else checkPalindromeCycle (iters + 1) atStep

    lychrelStep x = x + reverseNumber 10 x

-- Maximal digit sum. Given two numbers a,b < 100, what a^b produces a number with the largest sum of its digits?
--
-- This is likely a large number raised to a large power
problem56 :: Integer
problem56 = head . reverse $ sort [ (sum . iDigits $ a^b) | a <- [90..99], b <- [90..99] ]


-- The sqrt of 2 expressed as nested fractions happens to have an inductive algorithm for calculating the n+1-th
-- fraction.
--
-- Given numerator(n) and denom(n), numerator(n+1) = 2*denom(n) + numerator(n), denom(n+1) = denom(n) + numerator(n)
--
-- This was fun, if only because it required working around floating-point issues
problem57 =
  length . filter largerNum . take 1000 $ iterate step (3::Integer, 2::Integer)
  where
    step (num, denom) = (num + (2*denom), num+denom)

    largerNum (num, denom) = intLog10 num > intLog10 denom

data PrimeSpiral = PrimeSpiral {sideLen :: Int, psNumPrimes:: Int} deriving (Show)

-- problem58 :: Maybe PrimeSpiral
problem58 =
  find ( (< 0.10) . ratio). iterate computeLayer $ PrimeSpiral {sideLen= 3, psNumPrimes= 3}
  where
    ratio (PrimeSpiral n pxs) = fromIntegral pxs / fromIntegral (2 * n - 1)
    computeLayer spiralState = let
      sideLen' = sideLen spiralState + 2
      lowerRight = sideLen' ^ 2
      others = (\x -> lowerRight - (sideLen' -1) * x) <$> [1..3]
      numPrimes = length . filter (isPrime . fromIntegral) $ lowerRight:others
      in PrimeSpiral {sideLen= sideLen spiralState + 2,
                      psNumPrimes= psNumPrimes spiralState + numPrimes
                     }

-- Fun "Find the key" problem. I approached this by first determining how to evaluate a key's "goodness",
-- then relying on my own observation to select the correct key. From there's is just a mechanical process
-- to extract the sum
problem59 :: IO Int
problem59 = do
  contents <- readFile "src/Info/p059_cipher.txt"
  let charCodes = codes contents
      candidateKeys = filter (containsAClue . decode charCodes) allKeys
      messages = (\key -> (key, take 10 $ decode charCodes key)) <$> candidateKeys
  -- print messages
  let properKey = [101, 120, 112]
      fullMessage = decode charCodes properKey
      charSum = sum $ ord <$> unwords fullMessage
  print $ unwords fullMessage
  pure charSum
  where
  codes :: String -> [Int]
  codes = map read . words . fmap (\c -> if c == ',' then ' ' else c)
  decode message key = words . map chr $ zipWith xor message (concat $ repeat key)

  allKeys = [[a, b, c] | a <- [97..122], b <- [97..122], c <- [97..122]]
  clues = ["and", "the", "of"]
  containsAClue = not . null . intersect clues


problem67 :: Integer
problem67 = maximumPathPyramid DATA.problem67

funcOfRanges :: Ord a => (a -> a -> a) -> [a] -> M.Map a Int
funcOfRanges f range =
  M.fromList . foldl' accumulate [] $ zip range [1..]
  where
    accumulate [] a = [a]
    accumulate ((x, i):xs) (a, j) = (f a x, j) : (x, i) : xs

