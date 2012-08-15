import qualified Data.Map as Map (empty)
import Control.Monad.State (evalStateT)
import Control.Monad.Error (throwError)
import System.IO (stdin,stdout)
import Prelude hiding (getLine,map)
import OpenTheory.Name (Name(..))
import OpenTheory.Term (Term(..),Var(..),Const(..),rand,rator)
import OpenTheory.Type ((-->))
import OpenTheory.Equality (rhs)
import OpenTheory.Proof (Proof(Refl,AppThm),axiom,concl)
import OpenTheory.Proof (Proof(EqMp))
import OpenTheory.Rule (trans,spec,subs)
import OpenTheory.Conv (depthConv)
import OpenTheory.Bool (forall)
import OpenTheory.Natural (nsNum,num,eq)
import OpenTheory.Read (ReadState(ReadState),readTerm)
import qualified OpenTheory.Read as R (ReadState(..))
import OpenTheory.Write (WM,WriteState(WriteState),logThm,logRawLn)
import qualified OpenTheory.Write as W (WriteState(..))

data Norrish =
    NZero
  | NBit1 Norrish
  | NBit2 Norrish

data Binary =
    BZero
  | BBit0 Binary
  | BBit1 Binary

-- n2b n[Nor] = |- n[Nor] = n[Bin]
n2b :: Norrish -> Proof
n2b NZero = Refl zero
n2b (NBit1 n) = AppThm (Refl bit1_tm) (n2b n)
n2b (NBit2 n) = trans (subs 2 (n2b n) (spec (n2t n) th1)) (binc (BBit1 nb))
  where nb = t2b (rhs (concl (n2b n)))

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

bit_tm :: String -> Term
bit_tm s = ConstTerm (Const (nsNum ("bit"++s))) (num --> num)

bit0_tm :: Term
bit0_tm = bit_tm "0"

bit1_tm :: Term
bit1_tm = bit_tm "1"

bit2_tm :: Term
bit2_tm = bit_tm "2"

bit0 :: Term -> Term
bit0 = AppTerm bit0_tm

bit1 :: Term -> Term
bit1 = AppTerm bit1_tm

bit2 :: Term -> Term
bit2 = AppTerm bit2_tm

zero :: Term
zero = ConstTerm (Const (nsNum "zero")) num

suc :: Term -> Term
suc  = AppTerm (ConstTerm (Const (nsNum "suc")) (num --> num))

n2t :: Norrish -> Term
n2t NZero = zero
n2t (NBit1 n) = bit1 (n2t n)
n2t (NBit2 n) = bit2 (n2t n)

t2n :: Term -> Either String Norrish
t2n tm = if tm == zero then return NZero else
         case tm of
           (AppTerm f x) -> if f == bit1_tm then t2n x >>= (return . NBit1) else
                            if f == bit2_tm then t2n x >>= (return . NBit2) else
                            throwError "t2n"
           _ -> throwError "t2n"

t2b :: Term -> Binary
t2b tm = if tm == zero then BZero else
         if rator tm == bit0_tm then BBit0 (t2b (rand tm)) else
         if rator tm == bit1_tm then BBit1 (t2b (rand tm)) else error "t2b"

b2t :: Binary -> Term
b2t BZero = zero
b2t (BBit0 b) = bit0 (b2t b)
b2t (BBit1 b) = bit1 (b2t b)

write :: Term -> WM ()
write tm =
  case depthConv ((flip (>>=) (return . n2b)) . t2n) tm of
    Right th -> logThm (EqMp th (axiom tm)) -- logThm th
    Left err -> logRawLn err

main :: IO ()
main = do
  let rs = ReadState {R.handle=stdin, R.map=Map.empty, R.stack=[], R.thms=[]}
  tm <- evalStateT readTerm rs
  let ws = WriteState {W.handle=stdout, W.map=Map.empty}
  evalStateT (write tm) ws
