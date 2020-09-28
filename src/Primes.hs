module Primes
(
  primes
)
where

primes :: [Integer]
primes = 2:3:5: minus primeWheel (foldr (\p r-> p*p : union [p*p+p, p*p+2*p..] r) [] primes)
-- 2 : minus [3..] (foldr (\p r-> p*p : union [p*p+p, p*p+2*p..] r) [] primes)

primeWheel :: [Integer]
primeWheel = 7:11:13:17:19:23:29:31: turn [7, 11, 13, 17, 19, 23, 29, 31]
  where
    turn xs = let
      ys = (+ 30) <$> xs
      [a', b', c', d', e', f', g', h'] = ys
      in a':b':c':d':e':f':g':h': turn ys

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
