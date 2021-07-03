module FiftyToOneHundred where

import qualified Info.FiftyToOneHundred  as DATA
import EarlyProblems (maximumPathPyramid)
import qualified EarlyProblems as Funcs
import qualified Primes
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Monad.Trans (liftIO)
import Control.Monad.State.Strict (State, StateT, execStateT, evalState, runState, gets, modify)
import Data.Foldable (foldl', find, foldlM, maximumBy, minimumBy)
import Data.List (sort, (\\), sortOn, group, find, intersect, permutations)
import Data.Maybe (mapMaybe, fromMaybe, isJust)
import Data.Bits
import Data.Char (ord, chr)
import Data.Ord
import Math
import Probability
import Data.Number.Fixed
import Data.Ratio

import Debug.Trace

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
    primesLessThanOneMM = takeWhile (<= 1000000) Funcs.primes

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
    sameDigits l r =  ( sort  $ Funcs.digits l ) == ( sort  $ Funcs.digits r )
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
  (Funcs.factorial n) `div` ((Funcs.factorial r) * Funcs.factorial (n - r)) |
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
    checkPalindromeCycle 50 x = not . Funcs.palindromeNumber $ lychrelStep x
    checkPalindromeCycle iters x = let
      atStep = lychrelStep x
      in if Funcs.palindromeNumber atStep then False else checkPalindromeCycle (iters + 1) atStep

    lychrelStep x = x + Funcs.reverseNumber 10 x

-- Maximal digit sum. Given two numbers a,b < 100, what a^b produces a number with the largest sum of its digits?
--
-- This is likely a large number raised to a large power
problem56 :: Integer
problem56 = head . reverse $ sort [ (sum . Funcs.iDigits $ a^b) | a <- [90..99], b <- [90..99] ]


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
      numPrimes = length . filter (Funcs.isPrime . fromIntegral) $ lowerRight:others
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


-- Find the first prime group of 5 elements with the "concat" property
--
-- The property says that each element in the group, when concatinated with another
-- from the group form a prime. The order and elements do not matter.
--
-- It follows from this property's definiton that removing one of the primes from the group
-- does not break the concatination property. This new property means the groups of primes
-- can be built up inductively by the following algorithm:
--
-- primes = Generate a sorted list of N primes
-- possibleGroups = []
-- for each prime p in primes:
--    for each group possibleGroups:
--        if formsGroup(group, p) then addToGroup(group,p)
--        if length(group) == 5 then return group
--    addNewGroup([p], possibleGroups)
--
-- problem60 ::
problem60 = fmap sum . filter ((== 5) . length) . flip evalState M.empty $ foldlM concatProperty [] $ takeWhile (< 20000) Primes.primesLessThanTenMM
  where
    concatProperty [] p = pure [[p]]
    concatProperty (g:groups) p = do
      merged <- meomizedMerge p g
      case merged of
        Just g' -> ([g, g']<>) <$> concatProperty groups p
        Nothing -> (g:) <$> concatProperty groups p

    meomizedMerge p g = do
      isMatch <- all id <$> (mapM (concattedPrimes p) g)
      pure $ if isMatch then Just (p:g) else Nothing

    concattedPrimes :: Int -> Int -> State (M.Map (Int, Int) Bool) Bool
    concattedPrimes l r = do
      cachedValue <- gets (M.lookup (l, r))
      case cachedValue of
        Just v -> pure v
        Nothing ->  do
          let result = Primes.cryptoPrimeCheck (concatNumbers l r) &&
                       Primes.cryptoPrimeCheck (concatNumbers r l)
          modify (M.insert (l, r) result)
          modify (M.insert (r, l) result)
          pure result

-- Compute a six digit cycle using four digit figurate (meaning polygonal)
-- numbers. Figurate numbers are used to count the number of things that fit
-- inside a shape with side length of n
--
-- To do this efficiently, I'm going to pre-process all of the figurate numbers
-- from triangle->octagonal to facilitate easy lookup. From there, perform a DFS
-- through each set of numbers. There is only one cycle among 4 digit numbers, so
-- the first one found will be the answer.
--
-- The pre-processing step will, for each set of figurate numbers of size X, split
-- each number into a leading and trailing pair. Then, the numbers will be stored in
-- a Map Int [Int] for fast lookup.
--
-- To reconstruct the original numbers from the lookup table, store a list (stack) of the keys
-- as the search progresses. The result can be found by popping the head from the stack,
-- multiplying it by 100, then adding the next element. The first element must be preserved to
-- use as the final element's tens & ones places.
--
-- There is probably a DP solution as well, but I haven't thought through how it will work.
--
-- That actually really overcomplicates things. Instead, preprocess down to only the lists of
-- figurate numbers that have a suffix appearing as some other figurate prefix.
--
-- This is a rather gnarly solution. I ended up tripping myself up because the `matches` list was
-- empty on the final match, but I was attempting to `concatMap` across that list. This meant the
-- final member of the cycle was never added. Took me a solid 15 minutes to debug that.
problem61 :: Int
problem61 = let
  seeds = filter (\(_, _, _, i) -> i == 3) potentials
  rest = filter (differentFamily 3) potentials
  in sum . fmap (\(_, _, x, _) -> x) . head . filter (not . null) $ dfs [] rest <$> seeds
  where


    -- preprocessing
    tris = fourDigits triangleNumbers
    sqrs = fourDigits squareNumbers
    pents = fourDigits pentagonalNumbers
    hexs = fourDigits hexagonalNumbers
    hepts = fourDigits heptagonalNumbers
    octs = fourDigits octagonalNumbers

    nums (i, xs) = [(pre, suf, x, i) | x <- xs, let (pre, suf) = splitUp x]
    splits = nums <$> zip [3..] [tris, sqrs, pents, hexs, hepts, octs]

    potentials = [
      (pre, suf, x, i) |
      ls <- splits,
      let rest = concat $ filter (/= ls) splits,
      (pre, suf, x, i) <- ls,
      isJust $ find (\(pre', suf', _, _) -> pre == suf' || suf == pre') rest
      ]

    dfs xs [] (a, b, x, i)
      | isJust $ find (\(a', b', x', i') -> i' == 3 && a' == b) xs = xs
      | otherwise = []
    dfs xs rest (a,b,x,i) = let
      matches = filter (\(a', b', x', i') -> b == a' && i' /= i) rest
      remaining = filter (differentFamily i) rest
      in if null matches && not (null remaining)-- (trace (show (a,b,x,i)<> " " <> show matches <> " " <> show xs <> " " <> show (length remaining)) matches) && not (null remaining)
         then []
         else if not (null remaining)
            then concatMap (dfs ((a, b, x,i):xs) remaining) matches
            else dfs ((a, b, x,i):xs) remaining (a,b,x,i)


    differentFamily i (_, _, _, a) = i /= a

    fourDigits = takeWhile inRange . dropWhile (not . inRange)
    inRange x = x >= 1000 && x < 10000

    splitUp x = (x `div` 100, x `mod` 100)

-- This problem seeks to find the smallest cube such that the permutation of its digits are also cubes.
-- I settled on taking the first 10k cube because it was convenient. Obviously doesn't generalize well
problem62 :: Int
problem62 = minimum . concat . M.elems . M.filter ((== 5). length) . foldl f M.empty $ take 10000 cubes
  where
    f acc cube = M.insertWith (<>) (sort $ Funcs.digits cube) [cube] acc

-- Powerful digit counts. This seems to deal directly with number theory
--
-- The problem revolves around finding n-digit numbers that are also an n-th power.
-- Inside that, there's a question of how many digits a number will have when raised to the nth power.
-- Rasing to a power is repeated multiplication, and 10^2 results in an extra 0. Therefore, because
-- all numbers greater than 10 share this property - meaning they're at least as large as 10 - the only
-- numbers to evaluate are 1-9 being raised to powers until this property no longer holds.
--
-- Can find the number of digits resulting from a multiplication by taking the log_10 of each number,
-- adding them together, flooring the result, then adding 1. The log_10 determins how many places areAmicable
-- in each number b/c logarithm is just what you'd have to raise 10 to to get the original number. Adding two
-- logarithms is equivalent to multiplying them. Flooring drops down to the preceding power of 10, and adding 1 adds on
-- a 0 like you get when transitoning from 9 -> 10.
--
-- The problem asks for a specific and unbounded number, so there is some threshold or terminator,
-- after which there are no more "powerful numbers".
problem63 :: Int
problem63 = length [x^y |
    x <- [1..9],
    y <- [1..25],
    numDigits 1 (x^y) == y
    ]

-- This is a brute-force solution. I suspect there's a closed-form, but I
-- haven't noticed a pattern in where odd sequence lengths occur, so unfortunately
-- I'm stuck with massive precision operations.
problem64 :: [Int]
problem64 =
  [ sequenceLength (fromIntegral x) |
    x <- [1..10000],
    not (isPerfectSquare  x)
  ]
  where
    sequenceLength a = let
      a0 = sqrt a
      a0Floor = floor a0
      infFraction = (floor <$> iterate repeatedSqrtFractionStep a0):: [Int]
      in length $ takeWhile (/= (2 * a0Floor)) infFraction

    repeatedSqrtFractionStep :: Fixed Prec500 -> Fixed Prec500
    repeatedSqrtFractionStep a = 1/(a - fromIntegral (floor a))

problem65 :: Integer
problem65 = let
  eConvergents = 2:3:(8%3):(11%4):computeConvergents eSeq (8%3) (11%4)
  elem100 = eConvergents !! 99
  digitSum = sum . Funcs.iDigits $ numerator elem100
  in digitSum
  where
    eSeq :: [Integer]
    eSeq = concat [[1, 2*k, 1] | k <- [2..]]

    computeConvergents :: [Integer] -> Rational -> Rational -> [Rational]
    computeConvergents (k:restK) c'' c' = let
      num = (k * numerator c') + numerator c''
      den = (k * denominator c') + denominator c''
      c = num%den
      in c : computeConvergents restK c' c

-- this is pell's equation
problem66 :: Integer
problem66 =
  snd . maximumBy (comparing fst) $ minimalSolution <$> filter (not . isPerfectSquare . fromIntegral ) [2..1000]
  where
    minimalSolution d = head [(x, d) |
      cvgnt <- convergents  $ fromIntegral d,
      let x = numerator cvgnt,
      let y = denominator cvgnt,
      (x*x) - (d * (y*y)) == 1
      ]

problem67 :: Integer
problem67 = maximumPathPyramid DATA.problem67

--problem68 :: [[Int]]
problem68 = minimum <$> M.elems uniqueSolutions
  where
    -- generate all rings, in ascending clockwise order
    rings = [ fullRing |
      numbers <- choose 5 [1..9],
      let diff = [1..10] \\ numbers,
      orderings <- permutations numbers,
      let h = head orderings,
      outerNums <- permutations diff,
      let innerRing = orderings `zip` tail (orderings<>[h]),
      let fullRing = map (\((b,c), a) -> (a,b,c))$ innerRing `zip` outerNums,
      allSameSum fullRing
      ]

    tripleSum (a,b,c) = a+b+c
    allSameSum (x:xs) = let
      leadSum = tripleSum x
      in all (== leadSum) $ map tripleSum xs

    uniqueSolutions = foldl f M.empty rings
    f index ring = M.insertWith (<>) (sort ring) [ring] index

problem69 = [ (fromIntegral n / (fromIntegral $ totient n), n) | n <- [200000..300000]]

problem69Fast =
  rho <$> potentials
  where
    potentials = takeWhile (<= 1000000) [product p | n <- [2..], let p = take n (Primes.primes :: [Integer])]
    rho n = (fromIntegral  n / fromIntegral (totient n), n)

-- "Centering" the serach around sqrt(10^7) dramatically reduces the search space. This takes about 10 sec
problem70 = minimumBy (comparing thrd) [ (tot, x, fromIntegral x / fromIntegral tot) |
              p <- smallishPrimes,
              p' <- dropWhile (<= p) smallishPrimes,
              p' > p,
              let x = p * p',
              x <= 10^7,
              let tot = totient p * totient p',
              logBase 10 (fromIntegral x) - logBase 10 (fromIntegral tot) <= 0.01,
              sameDigits x tot
              ]
  where
    cap = (+  500). floor . head $ convergents (10^7)
    smallishPrimes = takeWhile (<= cap) Primes.primes
    sameDigits a b = sort (Funcs.iDigits a) == sort (Funcs.iDigits b)
    thrd (_, _, x) = x

problem71 = last $ go 0 2 5
  where
    target = 3 % 7

    go best n d
      | d > 10^6 = []
      | n % d > target = go best n (d+1)
      | n % d < target = let
        frac = n % d
        in if reducedProperFrac n d && frac > best
           then frac : go frac (n+1) d
           else go best (n+1) d
      | otherwise =  go best (n+1) d

problem72 = sum $ totients (10^6)

problem73 = sum [eligible d | d <- [4..12000]]
  where
    eligible :: Int -> Int
    eligible d =
      let a = ceiling $ fromIntegral d/3
          b = floor $ fromIntegral d/2
          fracs = [n | n <- [a..b], gcd n d == 1]
      in length fracs

problem74 = let
  additionalNumbers = exchange0For1 <$> filter (isJust . find (== 1) ) digs
  in sum $ length . unique . filter ((/= 0) . head) . permutations <$> digs<>additionalNumbers
  where
    digs = [ digs |
              n <- [1..6],
              digs <- unique . filter ((/= 0) . head) $  sort <$> chooseWithReplacement n [0..9],
              (== 60) . length $ factorialChain (fromIntegral  $ digitsToNumber (length digs -1) digs)
              ]
    digitsToNumber n (x:[]) = x
    digitsToNumber n (x:xs) = (x * (10^n)) + digitsToNumber (n-1) xs

    exchange0For1 [] = []
    exchange0For1 (1:xs) = 0 : exchange0For1 xs
    exchange0For1 (a:xs) = a : exchange0For1 xs

problem75 =  M.size $ M.filterWithKey (\k v -> length v == 1 && fromIntegral  k <= maxLen) perimeterLengths
  where
    maxLen = 1500000
    sideLengths = basePythagoreanTriplets 1000

    extend trip@(a,b,c) = let
      perim = perimeter trip
      cap = maxLen `div` perim
      extension = [(x*a, x*b, x*c)  | x <- [1..cap]]
      in extension

    allLengths = concatMap extend sideLengths

    perimeterLengths = foldl' (\acc trip -> M.insertWith mergeIfNew (perimeter trip) [trip] acc ) M.empty allLengths
    perimeter (a,b,c) = a + b + c


    mergeIfNew [(a,b,c)] known@[(a', b', c')]
      | (a == a' && b == b') || (a == b' && b == a') = known
      | otherwise = [(a', b', c'), (a,b,c)]
    mergeIfNew ls@[(a,b,c)] known@((a', b', c'):rest)
      | (a == a' && b == b') || (a == b' && b == a') = known
      | otherwise = (a', b', c'):mergeIfNew ls rest


-- Inspiration for this solution was taken from https://www.programminglogic.com/integer-partition-algorithm/
--
-- It works by recursing all the way to the "bottom" on one side, while slowly exploring from the top on the other. The
-- memoization table builds from the bottom-up as the waysB calculations run. These memoized values can then be reused at each
-- higher-level step, reducing the amount of work required the further along the algorithm runs.
--
-- I struggled to find the proper divide and conqueor aproach. I mistakenly was traversing [n-1, n-2..1] and memoizing those values, but
-- that's simply the powers of two. The parition function is something much more complicated
problem76 = last $ partitions 100

problem77 = zip [1..] $ evalState (traverse primePartitions [1..100]) M.empty
  where
    sopf = sum . primeFactors

    -- This is the euler transform applied to product(1/1-k^q)
    -- derived from https://math.stackexchange.com/questions/89240/prime-partition
    primePartitions :: Integer -> State (M.Map Integer Integer) Integer
    primePartitions 1 = pure 0
    primePartitions n = do
      known <- gets (M.lookup n)
      case known of
        Just ways -> pure ways
        Nothing -> do
          partialWays <- traverse (\j -> (* (sopf j)) <$> primePartitions (n-j)) [1..n-1]
          let ways = (sopf n + sum partialWays) `div` n
          modify (M.insert n ways)
          pure ways

problem78 =  partitionsEuler [(5 * n)+4| n <- [1..2000]]

-- Solved this with pencil + paper
problem79 = 42

problem80 =
    sum $ concat [
          take 100 (integers<>decimals) |
          n <- [1..100],
          not $ isPerfectSquare n,
          let (integers, decimals) = sqrtDigits 110 n
        ]

-- A very slow implementation that explores both branches
problem81 :: IO Int
problem81 = do
  rawLines <- T.lines <$> TIO.readFile "data/p081_matrix.txt"
  let matrix = Seq.fromList $ fmap (Seq.fromList . (map (read . T.unpack) :: [T.Text] -> [Int])) $ T.split (== ',') <$> rawLines
      origin = getFromMatrix matrix 0 0
      pathScores = search matrix (Seq.fromList [(0,0)]) S.empty (M.fromList [((0,0), origin)])
  pure $ pathScores M.! (boundary, boundary)

  where

    boundary = 79
    getFromMatrix m x y = (m `Seq.index` y) `Seq.index` x
    search matrix frontier seen scores =
      case Seq.viewl frontier of
        Seq.EmptyL ->
          scores
        ( v Seq.:< rest) | S.notMember v seen -> let
          (frontier', scores') = djikstra matrix rest seen scores v
          in search matrix frontier' (S.insert v seen) scores'
        ((x,y) Seq.:< rest) ->
          search matrix rest seen scores -- when (x,y) have been seen already, skip the point

    djikstra matrix frontier seen scores v@(x,y) = let
      frontierX = if x < boundary then frontier Seq.|> (x+1, y) else frontier
      frontier' = if y < boundary then frontierX Seq.|> (x, y+1) else frontierX
      scores' = updateScore matrix (updateScore matrix scores v (x+1, y)) v (x, y+1)
      in (frontier', scores')

    updateScore matrix scores from to@(x,y) = let
      vWeight = scores M.! from
      toVal = getFromMatrix matrix x y
      destScore = vWeight + toVal
      in
        case M.lookup to scores of
          Just knownScore | knownScore < destScore -> scores
          _ -> M.insert to destScore scores


problem82 = do
  rawLines <- T.lines <$> TIO.readFile "data/p082_matrix.txt"
  let matrix = Seq.fromList $ fmap (Seq.fromList . (map (read . T.unpack) :: [T.Text] -> [Int])) $ T.split (== ',') <$> rawLines
      origins = [((0, y), getFromMatrix matrix 0 y) | y <- [0..boundary]]
      boundaries = [(boundary, y) | y <- [0..boundary]]
      pathScores = (\o@(origin, _) -> (origin, search matrix (Seq.fromList [origin]) (M.fromList [o]))) <$> origins
      start (a,b,c) = a
  pure $ minimumBy (comparing start) [(scores M.! end, origin, end) | (origin, scores) <- pathScores, end <- boundaries]

  where

    boundary = 79
    getFromMatrix m x y = (m `Seq.index` y) `Seq.index` x
    search matrix frontier scores =
      case Seq.viewl frontier of
        Seq.EmptyL ->
          scores
        ( v Seq.:< rest) -> let
          (frontier', scores') = djikstra matrix rest scores v
          in search matrix frontier' scores'

    djikstra matrix frontier scores v@(x,y) = let
      neighbors = filter inBounds [(x, y-1), (x+1, y), (x, y+1)]
      scores' = foldl (updateScore matrix v) scores neighbors
      neighbors' = filter (\pt ->(fromMaybe (10^10) $ M.lookup pt scores ) > (scores' M.! pt)) neighbors
      frontier' = frontier Seq.>< Seq.fromList neighbors'
      in (frontier', scores')

    updateScore matrix from scores to@(x,y) = let
      vWeight = scores M.! from
      toVal = getFromMatrix matrix x y
      destScore = vWeight + toVal
      in
        case M.lookup to scores of
          Just knownScore | knownScore < destScore -> scores
          _ -> M.insert to destScore scores

    inBounds (x,y) = x <= boundary && y <= boundary && y >=0

problem83 :: IO Int
problem83 = do
  rawLines <- T.lines <$> TIO.readFile "data/p081_matrix.txt"
  let matrix = Seq.fromList $ fmap (Seq.fromList . (map (read . T.unpack) :: [T.Text] -> [Int])) $ T.split (== ',') <$> rawLines
      origin = getFromMatrix matrix 0 0
      pathScores = search matrix (Seq.fromList [(0,0)]) (M.fromList [((0,0), origin)])
  pure $ pathScores M.! (boundary, boundary)

  where

    boundary = 79
    getFromMatrix m x y = (m `Seq.index` y) `Seq.index` x
    search matrix frontier scores =
      case Seq.viewl frontier of
        Seq.EmptyL ->
          scores
        ( v Seq.:< rest) -> let
          (frontier', scores') = djikstra matrix rest scores v
          in search matrix frontier' scores'

    djikstra matrix frontier scores v@(x,y) = let
      neighbors = filter (\pt -> inBounds pt) [(x-1, y), (x+1, y), (x, y-1), (x, y+1)]
      scores' = foldl (updateScore matrix v) scores neighbors
      neighbors' = filter (\pt ->(fromMaybe (10^10) $ M.lookup pt scores ) > (scores' M.! pt)) neighbors
      frontier' = frontier Seq.>< Seq.fromList neighbors'
      in (frontier', scores')

    updateScore matrix from scores to@(x,y) = let
      vWeight = scores M.! from
      toVal = getFromMatrix matrix x y
      destScore = vWeight + toVal
      in
        case M.lookup (trace (show (from, to, vWeight, toVal, destScore)) to) scores of
          Just knownScore | knownScore < destScore -> scores
          _ -> M.insert to destScore scores

    inBounds (x,y) = x <= boundary && x >=0 && y <= boundary && y >=0

data MonopolyState =
  MonopolyState
  { ccCards :: Seq.Seq Int
  , chCards :: Seq.Seq Int
  , location :: Int
  , visits :: M.Map Int Int
  , previousTwoRolls :: [[Int]]
  } deriving Show

problem84 = do
  distributions <- traverse (const simulate) [1..1000]
  let pmf = foldl (\acc m ->
              foldl (\inner (k, v) ->
                  M.insertWith (+) k v inner) acc $ M.toList m)
              M.empty
              distributions
  pure pmf
  where
    boardSize = 40
    jail = 10
    dieFaces = 4
    numRolls = 2

    simulate :: IO (M.Map Int Int)
    simulate = do
      ccCards <- shuffle [1..16]
      cHCards <- shuffle [1..16]
      let state = MonopolyState
                    { ccCards = Seq.fromList ccCards
                    , chCards = Seq.fromList cHCards
                    , location = 0
                    , visits = M.empty
                    , previousTwoRolls = []
                    }
      fmap visits $ execStateT (mapM_ (const gameStep) [1..1000]) state

    gameStep :: StateT MonopolyState IO ()
    gameStep = do
      roll <- liftIO (rollDice dieFaces 2)
      let rollSum = sum roll
      rolls <- gets previousTwoRolls
      case rolls of
        [] -> do
          advance rollSum
          modify $ \s -> s { previousTwoRolls = [roll] }
        [r] -> do
          advance rollSum
          modify $ \s -> s { previousTwoRolls = [r, roll] }
        [rr, r] | doubles rolls && doubles r && doubles rr ->
          -- three doubles sends player to jail
          modify $ \s -> s { location = jail,
                             visits = M.insertWith  (+) jail 1 (visits s),
                             previousTwoRolls = [r, roll]
                           }
        [rr, r] -> do
          advance rollSum
          modify $ \s -> s { previousTwoRolls = [r, roll] }

    advance :: Int -> StateT MonopolyState IO ()
    advance roll = do
      landing <- (`mod` 40) . (+ roll) <$> gets location

      case landing of
        2 -> handleDraw drawCC landing
        7 -> handleDraw (drawCH landing) landing
        17 -> handleDraw drawCC landing
        22 -> handleDraw (drawCH landing) landing
        30 -> trackMove jail
        33 -> handleDraw drawCC landing
        36 -> handleDraw (drawCH landing) landing
        _ -> trackMove landing
      where
        handleDraw deck landing = do
          res <- deck
          case res of
            Just dest -> trackMove dest
            Nothing -> trackMove landing

        trackMove :: Int -> StateT MonopolyState IO ()
        trackMove loc = modify $ \s -> s { location = loc, visits = M.insertWith  (+) loc 1 (visits s) }

        drawCC :: StateT MonopolyState IO (Maybe Int)
        drawCC = do
          (card, cards) <- gets (draw . ccCards)
          let dest = case card of
                      1 -> Just 0
                      2 -> Just jail
                      _ -> Nothing
          modify $ \s -> s {ccCards = cards}
          pure dest

        drawCH :: Int -> StateT MonopolyState IO (Maybe Int)
        drawCH landing = do
          (card, cards) <- gets (draw . chCards)
          let dest = case card of
                      1 -> Just 0
                      2 -> Just jail
                      3 -> Just 11
                      4 -> Just 24
                      5 -> Just 39
                      6 -> Just 5
                      7 -> maybe (Just 5) Just $ find (> landing) [5, 15, 25, 35] -- Go to the next railroad
                      8 -> maybe (Just 5) Just $ find (> landing) [5, 15, 25, 35]
                      9 -> maybe (Just 12) Just $ find (> landing) [12, 28]
                      10 -> Just $ (landing - 3)
                      _ -> Nothing
          modify $ \s -> s {chCards = cards}
          pure dest

        draw cards = let
          (card Seq.:< rest) = Seq.viewl cards
          in (card, rest Seq.|> card)

    doubles [a,b] = a == b

problem85 = [ (rows * cols, rects, rows, cols) |
  rows <- [1..1000],
  cols <- [1..rows],
  let rowRects = sum [1..cols],
  let rects = (* rowRects) $ sum [1..rows],
  abs(2000000 - rects) < 500
  ]



funcOfRanges :: Ord a => (a -> a -> a) -> [a] -> M.Map a Int
funcOfRanges f range =
  M.fromList . foldl' accumulate [] $ zip range [1..]
  where
    accumulate [] a = [a]
    accumulate ((x, i):xs) (a, j) = (f a x, j) : (x, i) : xs

