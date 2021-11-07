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

problem101 :: [Fixed Prec10]
problem101 = [ lagrangeInterpolation (take n basePoints) (fromIntegral n) | n <- [1..10]]
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

testBaseSeq len = (^3) <$> [1..len]
