module OneHundredToOneFifty where

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
import Control.Monad (guard)
import Control.Monad.Trans (liftIO)
import Control.Monad.State.Strict (State, StateT, execStateT, evalState, runState, gets, modify, put, get)
import Data.Foldable (foldl', find, foldlM, maximumBy, minimumBy)
import Data.List (sort, (\\), sortOn, group, find, intersect, permutations, partition, isPrefixOf)
import Data.Maybe (mapMaybe, fromMaybe, isJust, catMaybes)
import Data.Bits
import Data.Char (ord, chr)
import Data.Ord
import Math
import Probability
import Data.Number.Fixed
import Data.Ratio

import Debug.Trace

problem101 :: Int
problem101 = let
  steps = [lagrangeInterpolation (take n basePoints) (fromIntegral n) | n <- [1..10]] :: [Fixed Prec10]
  in sum $ fmap floor steps
  where
  basePoints = zip [0..] $ baseSequence 100.0

  lagrangeInterpolation points target =
    sum [ term |
          (xi, yi) <- points,
          let term = foldl' (lagrangeStep target xi) yi points
        ]

  lagrangeStep target xi term (xj, _)
    | xi /= xj = term * ((target - xj) / (xi - xj))
    | otherwise = term

  baseSequence len = generatingFunc <$> [1..len]
  generatingFunc n = sum [ coef * (n^pow) | pow <- [0..10], let coef = if even pow then 1 else -1 ]

-- Take a sequence of points on the euclidean plane and produce a convex shape that
-- bounds all the points. This shape's points are necessarily a subset of the full
-- set of points provided
convexHull :: [(Int, Int)] -> [(Int, Int)]
convexHull points = let
  upper = convexScan (take 2 orderedPoints) (drop 2 orderedPoints)
  lower = convexScan (take 2 $ reverse  orderedPoints) (drop 2 $ reverse  orderedPoints)
  in unique (upper <> lower)
  where
    orderedPoints = sortOn fst points

    convexScan fixedHull [] = fixedHull
    convexScan (b:c:fixedHull) (p:rest) = let
      makesRightTurn = ensureRightTurn [p,b,c]
      in if makesRightTurn
         then convexScan (p:b:c:fixedHull) rest -- continue on
         else convexScan (c:fixedHull) (p:rest) -- Drop the "middle" (b) element and retry


    -- This approach ignores when crossProduct == 0, which occurs when the three points
    -- are colinear. This means the resulting hull may include more points that necessary
    ensureRightTurn [p,li,li'] = let
      crossProduct = ((fst li - fst li') * (snd p - snd li')) - ((snd li - snd li') * (fst p - fst li'))
      in (crossProduct <= 0)

-- problem102 :: IO Int
-- problem102 = do
--  raw <- TIO.readFile "data/p102_triangles.txt"
--  let points = parsePoints raw
--  where
--    parsePoints line = pairs . fmap read T.splitOn (","::T.Text)
--

