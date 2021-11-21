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
import Data.Foldable (foldl', find, foldlM, maximumBy, minimumBy, toList)
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
  upper = convexScan (Seq.take 2 orderedPoints) (Seq.drop 2 orderedPoints)
  lower = convexScan (Seq.take 2 $ Seq.reverse orderedPoints) (Seq.drop 2 $ Seq.reverse orderedPoints)
  in unique $ toList (upper <> lower)
  where
    orderedPoints = Seq.fromList $ sortOn fst points
    (first Seq.:<| _)  =  orderedPoints

    convexScan fixedHull Seq.Empty = fixedHull
    convexScan (_ Seq.:<| Seq.Empty) _ = error "impossible state in ConvexHull: Singleton list"
    convexScan partialHull@(fixedHull Seq.:|> li' Seq.:|> li) (p Seq.:<| rest) = let
      hullStep = reduceToValidHull (partialHull Seq.:|> p)
      in convexScan hullStep rest

    reduceToValidHull hull@(fixedHull Seq.:|> li' Seq.:|> li Seq.:|> p) =
      if ensureRightTurn (p, li, li')
      then hull
      else reduceToValidHull (fixedHull Seq.:|> li' Seq.:|> p)
    reduceToValidHull hull@(Seq.Empty Seq.:|> li' Seq.:|> li) = hull

    -- This approach ignores when crossProduct == 0, which occurs when the three points
    -- are colinear. This means the resulting hull may include more points that necessary
    ensureRightTurn xs@(p, li, li') = let
      crossProduct = ((fst li - fst li') * (snd p - snd li')) - ((snd li - snd li') * (fst p - fst li'))
      in crossProduct < 0

-- problem102 :: IO Int
problem102 = do
  raw <- T.lines <$> TIO.readFile "data/p102_triangles.txt"
  let triangles = parsePoints <$> raw
      -- matches = [ 1 | points <- triangles, let hull = convexHull ((0, 0):points), sort points == sort hull]
      matches = [ points | points <- triangles, let hull = convexHull ((0, 0):points), sort points == sort hull]
  print $ length matches
  where
    parsePoints :: T.Text -> [(Int, Int)]
    parsePoints line = pairs . fmap (read . T.unpack) $ T.split (== ',') line


