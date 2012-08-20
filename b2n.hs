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
import OpenTheory.Natural.Numeral (Norrish(..),Binary(..),n2t,t2n,t2b,bit1,bit0,bit2,bit0_tm,bit1_tm,zero)
import OpenTheory.Read (ReadState(ReadState),readTerm)
import qualified OpenTheory.Read as R (ReadState(..))
import OpenTheory.Write (WM,WriteState(WriteState),logThm)
import qualified OpenTheory.Write as W (WriteState(..))

-- b2n n[Bin] = |- n[Bin] = n[Nor]
b2n :: Binary -> Proof
b2n BZero = Refl zero
b2n (BBit0 n) = trans (AppThm (Refl bit0_tm) (b2n n)) $ bdub (fromJust (t2n (rhs (concl (b2n n)))))
b2n (BBit1 n) = AppThm (Refl bit1_tm) (b2n n)

-- bdub n[Nor] = |- bit0 n[Nor] = (2*n)[Nor]
bdub :: Norrish -> Proof
bdub NZero = th1
bdub (NBit1 n) = subs 1 (bdub n) (spec (n2t n) th2)
bdub (NBit2 n) = (spec (n2t n) th3)

th1 :: Proof
th1 = axiom $ eq (bit0 zero) zero

th2 :: Proof
th2 = axiom $ forall vn $ eq (bit0 (bit1 tn)) (bit2 (bit0 tn))

th3 :: Proof
th3 = axiom $ forall vn $ eq (bit0 (bit2 tn)) (bit2 (bit1 tn))

vn :: Var
vn = Var (Name ([],"n"),num)

tn :: Term
tn  = VarTerm vn

write :: Bool -> Term -> WM ()
write b tm = f $ fromJust $ depthConv ((flip (>>=) (return . b2n)) . t2b) tm where
  f = if b then logThm . flip EqMp (axiom tm) else logThm

data Options = Rule | Help

options :: [OptDescr Options]
options =
  [ Option ['r'] ["rule"] (NoArg Rule) "return t |- t' instead of |- t = t'"
  , Option ['h'] ["help"] (NoArg Help) "print this help"
  ]

usage :: String
usage = usageInfo "b2n: convert binary numerals to Norrish" options

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
