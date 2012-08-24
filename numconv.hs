import qualified Data.Map as Map (empty)
import Data.Maybe (fromJust)
import Control.Monad.State (evalStateT)
import System.IO (stdin,stdout,stderr,hPutStr)
import System.Exit (exitSuccess,exitFailure)
import System.Environment (getArgs)
import System.Console.GetOpt (getOpt,ArgOrder(Permute),usageInfo,ArgDescr(NoArg),OptDescr(Option))
import Prelude hiding (getLine,map)
import OpenTheory.Term (Term(VarTerm),Var,var)
import OpenTheory.Equality (rhs)
import OpenTheory.Proof (Proof(Refl,AppThm),axiom,concl)
import OpenTheory.Proof (Proof(EqMp))
import OpenTheory.Rule (trans,spec,subs)
import OpenTheory.Conv (depthConv)
import OpenTheory.Bool (forall)
import OpenTheory.Natural (num,eq)
import OpenTheory.Natural.Numeral (Norrish(..),Binary(..),n2t,t2n,b2t,t2b,bit1,bit0,bit2,bit0_tm,bit1_tm,zero,suc)
import OpenTheory.Read (ReadState(ReadState),readTerm)
import qualified OpenTheory.Read as R (ReadState(..))
import OpenTheory.Write (WM,WriteState(WriteState),logThm)
import qualified OpenTheory.Write as W (WriteState(..))

-- n2b n[Nor] = |- n[Nor] = n[Bin]
n2b :: Norrish -> Proof
n2b NZero = Refl zero
n2b (NBit1 n) = AppThm (Refl bit1_tm) (n2b n)
n2b (NBit2 n) = trans (subs 2 (n2b n) (spec (n2t n) bit2SucBit1)) (binc (BBit1 nb))
  where nb = fromJust $ t2b $ rhs $ concl $ n2b n

-- binc n[Bin] = |- suc n[Bin] = (n+1)[Bin]
binc :: Binary -> Proof
binc BZero = sucZeroBit1Zero
binc (BBit0 n) = spec (b2t n) sucBit0Bit1
binc (BBit1 n) = subs 1 (binc n) (spec (b2t n) sucBit1Bit0Suc)

bit2SucBit1, sucZeroBit1Zero, sucBit0Bit1, sucBit1Bit0Suc :: Proof
bit2SucBit1     = axiom $ forall vn $ eq (bit2 tn) (suc (bit1 tn))
sucZeroBit1Zero = axiom $ eq (suc zero) (bit1 zero)
sucBit0Bit1     = axiom $ forall vn $ eq (suc (bit0 tn)) (bit1 tn)
sucBit1Bit0Suc  = axiom $ forall vn $ eq (suc (bit1 tn)) (bit0 (suc tn))

-- b2n n[Bin] = |- n[Bin] = n[Nor]
b2n :: Binary -> Proof
b2n BZero = Refl zero
b2n (BBit0 n) = trans (AppThm (Refl bit0_tm) (b2n n)) $ bdub (fromJust (t2n (rhs (concl (b2n n)))))
b2n (BBit1 n) = AppThm (Refl bit1_tm) (b2n n)

-- bdub n[Nor] = |- bit0 n[Nor] = (2*n)[Nor]
bdub :: Norrish -> Proof
bdub NZero = bit0Zero
bdub (NBit1 n) = subs 1 (bdub n) (spec (n2t n) bit0Bit1Bit2Bit0)
bdub (NBit2 n) = (spec (n2t n) bit0Bit2Bit2Bit1)

bit0Zero, bit0Bit1Bit2Bit0, bit0Bit2Bit2Bit1 :: Proof
bit0Zero         = axiom $ eq (bit0 zero) zero
bit0Bit1Bit2Bit0 = axiom $ forall vn $ eq (bit0 (bit1 tn)) (bit2 (bit0 tn))
bit0Bit2Bit2Bit1 = axiom $ forall vn $ eq (bit0 (bit2 tn)) (bit2 (bit1 tn))

vn :: Var; tn :: Term
vn = var "n" num
tn  = VarTerm vn

data Direction = N2B | B2N
data Rule = Conv | Rule
data Options = Options { help :: Bool, dir :: Direction, rule :: Rule }

write :: Options -> Term -> WM ()
write opts tm = f $ fromJust $ depthConv conv tm where
  f = case opts of
        Options {rule=Conv} -> logThm
        Options {rule=Rule} -> logThm . flip EqMp (axiom tm)
  conv = case opts of
           Options {dir=N2B} -> mk (t2n,n2b)
           Options {dir=B2N} -> mk (t2b,b2n)
         where mk (t2x,x2y) = (flip (>>=) (return . x2y)) . t2x

defaultOptions :: Options
defaultOptions = Options
  { help = True
  , dir = N2B
  , rule = Conv
  }

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['n'] ["n2b"] (NoArg (\o -> o {dir = N2B, help = False})) "convert Norrish to binary"
  , Option ['b'] ["b2n"] (NoArg (\o -> o {dir = B2N, help = False})) "convert binary to Norrish"
  , Option ['c'] ["conv"] (NoArg (\o -> o {rule = Conv, help = False})) "return |- t = t' (default)"
  , Option ['r'] ["rule"] (NoArg (\o -> o {rule = Rule, help = False})) "return t |- t' instead of |- t = t'"
  , Option ['h'] ["help"] (NoArg (\o -> o {help = True})) "print this help"
  ]

usage :: String
usage = flip usageInfo options $
  init $ unlines
    ["usage: numconv (-n | -b) [-rc]"
    ,"converts numerals between binary and Norrish encodings"
    ,"reads article from stdin and writes article to stdout"
    ]

main :: IO ()
main = do
  args <- getArgs
  opts <-
    case getOpt Permute options args of
      (o,[],[]) -> return $ foldl (flip id) defaultOptions o
      (_,_,errs) -> hPutStr stderr (concat errs ++ usage) >> exitFailure
  case opts of { Options {help=True} -> putStr usage >> exitSuccess ; _ -> return () }
  let rs = ReadState {R.handle=stdin, R.map=Map.empty, R.stack=[], R.thms=[]}
  tm <- evalStateT readTerm rs
  let ws = WriteState {W.handle=stdout, W.map=Map.empty}
  evalStateT (write opts tm) ws
