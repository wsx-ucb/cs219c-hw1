import Control.Monad.State
import Data.Char
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Void
import Shared
import System.Environment
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

type Dict a = Scoped (Map a Int)

resolve :: Ord a => a -> Dict a -> (Int, Dict a)
resolve name d@(Scoped (map, m)) =
  case Map.lookup name map of
    Just i -> (i, d)
    Nothing -> (i, Scoped (Map.insert name i map, i)) where i = m + 1

type Parser = StateT (Dict String) (Parsec Void String)

data Constraint = Constraint [(Bool, Int)] Int deriving (Show)

data Constraint' = Constraint' Bool [Int] Int deriving (Show)

pConstraints :: Parser (Scoped [Constraint])
pConstraints = do
  constraints <- pConstraint `sepBy1` symbol "&"
  b <- gets bound
  return $ Scoped (constraints, b)
  where
    sc = L.space space1 empty empty
    lexeme = L.lexeme sc
    symbol = L.symbol sc
    pConstraint = do
      ls <- pLiteral `sepBy1` symbol "+"
      _ <- symbol "<="
      bound <- lexeme L.decimal
      return $ Constraint ls bound
    pLiteral = do
      neg <- optional (char '-')
      name <- lexeme $ some (satisfy isAsciiAlpha)
      i <- state (resolve name)
      return (isNothing neg, i)
    isAsciiAlpha c = isAsciiLower c || isAsciiUpper c

adapter :: Scoped [Constraint] -> Scoped [Constraint']
adapter (Scoped (cs, n)) =
  let (cs1, Scoped (map, n')) = runState (mapM helper cs) (Scoped (Map.empty, n))
      cs2 = [Constraint' leq [p, n] 1 | (p, n) <- Map.toList map, leq <- [True, False]]
   in Scoped (cs1 ++ cs2, n')
  where
    helper :: Constraint -> State (Dict Int) Constraint'
    helper (Constraint ls b) = do
      vs <- mapM (\(p, v) -> if p then return v else state (resolve v)) ls
      return $ Constraint' True vs b

bailleux :: Scoped [Constraint'] -> Scoped Formula
bailleux (Scoped (cs, n)) = Scoped $ runState (And <$> mapM psi cs) n

psi :: Constraint' -> State Int Formula
psi (Constraint' leq vs b) = do
  (tot, ss) <- totalizer vs
  return $ And [tot, comparator leq ss b]

comparator :: Bool -> [Int] -> Int -> Formula
comparator True vs b = And [Not (Var v) | v <- drop b vs]
comparator False vs b = And [Var v | v <- take b vs]

totalizer :: [Int] -> State Int (Formula, [Int])
totalizer [v] = return (TrueF, [v])
totalizer vs = do
  let (vs1, vs2) = splitAt (length vs `div` 2) vs
  (f1, ss1) <- totalizer vs1
  (f2, ss2) <- totalizer vs2
  (f, ss) <- eq ss1 ss2
  return (And [f, f1, f2], ss)
  where
    freshVars n = do
      s <- get
      modify (+ n)
      return [(s + 1) .. (s + n)]
    eq :: [Int] -> [Int] -> State Int (Formula, [Int])
    eq ss1 ss2 = do
      ss <- freshVars (length ss1 + length ss2)
      let as = [TrueF] ++ map Var ss1 ++ [FalseF]
      let bs = [TrueF] ++ map Var ss2 ++ [FalseF]
      let rs = [TrueF] ++ map Var ss ++ [FalseF]
      let c1 a b s = Or [Not (as !! a), Not (bs !! b), rs !! s]
      let c2 a b s = Or [as !! (a + 1), bs !! (b + 1), Not (rs !! (s + 1))]
      let f = And [And [c1 ai bi si, c2 ai bi si] | ai <- [0 .. (length ss1)], bi <- [0 .. (length ss2)], si <- [0 .. (length ss)], ai + bi == si]
      return (f, ss)

main :: IO ()
main = do
  args <- (!! 0) <$> getArgs
  let Right cs = runParser (evalStateT pConstraints (Scoped (Map.empty, 0))) "" args
  res <- sat . bailleux . adapter $ cs
  print res
