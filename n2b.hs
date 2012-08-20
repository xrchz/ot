import qualified Data.Map as Map (empty)
import Data.Maybe (fromJust)
import Control.Monad.State (evalStateT)
import System.IO (stdin,stdout,stderr,hPutStr)
import System.Exit (exitSuccess,exitFailure)
import System.Environment (getArgs)
import System.Console.GetOpt (getOpt,ArgOrder(Permute),usageInfo,ArgDescr(NoArg),OptDescr(Option))
import Prelude hiding (getLine,map)
import OpenTheory.Name (Name(..))
import OpenTheory.Term (Term(..),Var(..))
import OpenTheory.Equality (rhs)
import OpenTheory.Proof (Proof(Refl,AppThm),axiom,concl)
import OpenTheory.Proof (Proof(EqMp))
import OpenTheory.Rule (trans,spec,subs)
import OpenTheory.Conv (depthConv)
import OpenTheory.Bool (forall)
import OpenTheory.Natural (num,eq)
import OpenTheory.Natural.Numeral (Norrish(..),Binary(..),n2t,t2n,b2t,t2b,bit1,bit0,bit2,bit1_tm,zero,suc)
import OpenTheory.Read (ReadState(ReadState),readTerm)
import qualified OpenTheory.Read as R (ReadState(..))
import OpenTheory.Write (WM,WriteState(WriteState),logThm)
import qualified OpenTheory.Write as W (WriteState(..))

-- n2b n[Nor] = |- n[Nor] = n[Bin]
n2b :: Norrish -> Proof
n2b NZero = Refl zero
n2b (NBit1 n) = AppThm (Refl bit1_tm) (n2b n)
n2b (NBit2 n) = trans (subs 2 (n2b n) (spec (n2t n) th1)) (binc (BBit1 nb))
  where nb = fromJust $ t2b $ rhs $ concl $ n2b n

-- binc n[Bin] = |- suc n[Bin] = (n+1)[Bin]
binc :: Binary -> Proof
binc BZero = th2
binc (BBit0 n) = spec (b2t n) th3
binc (BBit1 n) = subs 1 (binc n) (spec (b2t n) th4)

th1 :: Proof
th1 = axiom (forall vn (eq (bit2 tn) (suc (bit1 tn))))

th2 :: Proof
th2 = axiom (eq (suc zero) (bit1 zero))

th3 :: Proof
th3 = axiom (forall vn (eq (suc (bit0 tn)) (bit1 tn)))

th4 :: Proof
th4 = axiom (forall vn (eq (suc (bit1 tn)) (bit0 (suc tn))))

vn :: Var
vn = Var (Name ([],"n"),num)

tn :: Term
tn  = VarTerm vn

write :: Bool -> Term -> WM ()
write b tm = f $ fromJust $ depthConv ((flip (>>=) (return . n2b)) . t2n) tm where
  f = if b then logThm . flip EqMp (axiom tm) else logThm

data Options = Rule | Help

options :: [OptDescr Options]
options =
  [ Option ['r'] ["rule"] (NoArg Rule) "return t |- t' instead of |- t = t'"
  , Option ['h'] ["help"] (NoArg Help) "print this help"
  ]

usage :: String
usage = usageInfo "n2b: convert Norrish numerals to binary" options

main :: IO ()
main = do
  args <- getArgs
  rule <-
    case getOpt Permute options args of
      ([Rule],[],[]) -> return True
      ([Help],[],[]) -> putStr usage >> exitSuccess
      ([],[],[]) -> return False
      (_,_,errs) -> hPutStr stderr (concat errs ++ usage) >> exitFailure
  let rs = ReadState {R.handle=stdin, R.map=Map.empty, R.stack=[], R.thms=[]}
  tm <- evalStateT readTerm rs
  let ws = WriteState {W.handle=stdout, W.map=Map.empty}
  evalStateT (write rule tm) ws
