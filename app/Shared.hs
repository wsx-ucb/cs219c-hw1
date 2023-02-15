module Shared where

import Control.Arrow
import Control.Monad.State
import Data.DecisionDiagram.BDD
import Data.List
import Data.Maybe
import System.Exit
import System.Process

newtype Scoped a = Scoped (a, Int) deriving (Show)

bound :: Scoped a -> Int
bound (Scoped (_, i)) = i

data Formula
  = Var Int
  | Not Formula
  | Junct Bool [Formula]

instance Show Formula where
  show TrueF = "T"
  show FalseF = "F"
  show (Var i) = "v" ++ show i
  show (Not f) = "¬" ++ show f
  show (And fs) = "(" ++ intercalate " ∧ " (map show fs) ++ ")"
  show (Or fs) = "(" ++ intercalate " ∨ " (map show fs) ++ ")"

{-# COMPLETE Var, Not, Junc #-}

pattern Junc :: Bool -> [Formula] -> Formula
pattern Junc p fs <- Junct p fs
  where
    Junc p fs = Junct p $ concatMap (junc p) fs
      where
        junc _ (Junc _ [f]) = junc p f
        junc p (Junc p' fs) | p == p' = concatMap (junc p) fs
        junc p f = [f]

{-# COMPLETE Var, Not, And, Or #-}

pattern And, Or :: [Formula] -> Formula
pattern And fs = Junc True fs
pattern Or fs = Junc False fs

pattern TrueF, FalseF :: Formula
pattern TrueF = And []
pattern FalseF = Or []

data Literal = Literal Bool Int deriving (Show)

pattern Pos, Neg :: Int -> Literal
pattern Pos i = Literal True i
pattern Neg i = Literal False i

lit :: Bool -> Literal -> Literal
lit True l = l
lit False (Literal p i) = Literal (not p) i

type CNF = [[Literal]]

cnf :: Scoped Formula -> Scoped CNF
cnf (Scoped (f, n)) = Scoped $ runState (toCNF f) n

toCNF :: Formula -> State Int CNF
toCNF (And fs) = concat <$> mapM toCNF fs
toCNF f = uncurry (:) <$> toCNF' f
  where
    toCNF' (Or fs) = (concat *** concat) <$> mapAndUnzipM toCNF' fs
    toCNF' f = first singleton <$> tseytin f

tseytin :: Formula -> State Int (Literal, CNF)
tseytin (Var i) = return (Pos i, [])
tseytin (Not f) = first (lit False) <$> tseytin f
tseytin (Junc p fs) = do
  (ls, clss) <- mapAndUnzipM tseytin fs
  v <- do modify (+ 1); get
  let cls = (Literal p v : map (lit (not p)) ls) : [[Literal (not p) v, lit p l] | l <- ls]
  return (Pos v, cls ++ concat clss)

dimacs :: Scoped CNF -> String
dimacs (Scoped (cls, v)) =
  "p cnf "
    ++ show v
    ++ " "
    ++ show (length cls)
    ++ "\n"
    ++ intercalate "\n" (map showClause cls)
  where
    showClause = unwords . map showLiteral . (++ [Pos 0])
    showLiteral (Literal p i) = (if p then "" else "-") ++ show i

bdd :: Formula -> BDD AscOrder
bdd (Var i) = var i
bdd (Not f) = notB (bdd f)
bdd (Junc p fs) = (if p then andB else orB) (map bdd fs)

sat :: Scoped Formula -> IO Bool
sat f = do
  writeFile "test.cnf" (dimacs $ cnf f)
  code <- system "kissat -q test.cnf"
  return (code == ExitFailure 10)

sat' :: Scoped Formula -> IO Bool
sat' (Scoped (f, _)) = return $ isJust (anySat (bdd f))
