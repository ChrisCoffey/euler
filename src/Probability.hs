module Probability where

import System.Random

-- | Roll an n sided die, choosing a value from a uniform distribution
rollDie :: Int -> IO Int
rollDie sides = randomRIO (1, sides)

rollDice :: Int -> Int -> IO [Int]
rollDice sides numDice = mapM (const $ randomRIO (1, sides)) [1..numDice]

shuffle :: [a] -> IO [a]
shuffle ls = go (length ls) ls
  where
    go _ [] = pure []
    go _ [a] = pure [a]
    go n xs = do
      idx <- randomRIO (0, n-1)
      let front = take idx xs
          back = drop idx xs
          x = head back
      (x:) <$> go (n-1) (front++tail back)
