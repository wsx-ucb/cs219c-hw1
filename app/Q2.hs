import Data.List
import Criterion.Main

import Shared

pigeon :: Int -> Scoped Formula
pigeon n = Scoped (And [c1s, c2s], n * (n - 1))
  where
    v i j = Var ((i - 1) * (n - 1) + j)
    c1s = And [Or [v i j | j <- [1 .. (n - 1)]] | i <- [1 .. n]]
    c2s = And [Or [Not (v i k), Not (v j k)] | k <- [1 .. (n - 1)], i <- [1 .. n], j <- [1 .. (i - 1)]]

pigeon' :: Int -> Scoped Formula
pigeon' n = Scoped (And [c1s, c2s], n * k)
  where
    k = log2 (n - 1) + 1
    v i j = Var ((i - 1) * k + j)
    bn = zip [1 .. k] (toBin (n - 1) k)
    c1 i = foldl' (\r (j, w) -> Junct (not w) [Not (v i j), r]) FalseF bn
    c2 i j = Or [Or [And [Not (v i l), v j l], And [v i l, Not (v j l)]] | l <- [1 .. k]]
    c1s = And [c1 i | i <- [1 .. n]]
    c2s = And [c2 i j | i <- [1 .. n], j <- [1 .. (i - 1)]]
    toBin n 0 = []
    toBin n k = let (q, r) = n `divMod` 2 in (r == 1) : toBin q (k - 1)
    log2 1 = 0
    log2 n = 1 + log2 (n `div` 2)

main :: IO ()
main = do
  let naiveSat = map (\i -> bench (show i) . whnfIO . sat . pigeon $ i) [4 .. 10]
  let naiveBDD = map (\i -> bench (show i) . whnfIO . sat' . pigeon $ i) [4 .. 10]
  let altSat = map (\i -> bench (show i) . whnfIO . sat . pigeon' $ i) [4 .. 10]
  let altBDD = map (\i -> bench (show i) . whnfIO . sat' . pigeon' $ i) [4 .. 10]
  defaultMain [bgroup "Naive SAT" naiveSat, bgroup "Naive BDD" naiveBDD, bgroup "Alternative SAT" altSat, bgroup "Alternative BDD" altBDD]
