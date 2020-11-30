{-# GHC_OPTIONS MagicHash #-}
module Math where

import qualified Data.Set as Set
import Data.List (sort, group)
import GHC.Integer.Logarithms
import GHC.Exts

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
