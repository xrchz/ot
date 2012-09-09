-- |Natural number numeral terms.
module OpenTheory.Natural.Numeral(
zero,suc,
Norrish(..),n2t,t2n,
Binary(..),b2t,t2b,
bit0_tm,bit1_tm,bit2_tm,
bit0,bit1,bit2) where
import Control.Monad (mzero)
import OpenTheory.Type ((-->))
import OpenTheory.Term (Term(ConstTerm,AppTerm),Const(Const))
import OpenTheory.Natural (nsNum,num)

-- |Zero term.
zero :: Term
zero = ConstTerm (Const (nsNum "zero")) num

-- |Successor term.
suc :: Term -> Term
suc  = AppTerm (ConstTerm (Const (nsNum "suc")) (num --> num))

bit_tm :: String -> Term
bit_tm s = ConstTerm (Const (nsNum ("bit"++s))) (num --> num)

-- |Bit term: a function of type @num -> num@ intended to represent a digit in a numeral.
bit0_tm, bit1_tm, bit2_tm :: Term
bit0_tm = bit_tm "0"
bit1_tm = bit_tm "1"
bit2_tm = bit_tm "2"

-- |Numeral constructor: prepend a digit onto a numeral.
bit0, bit1, bit2 :: Term -> Term
bit0 = AppTerm bit0_tm
bit1 = AppTerm bit1_tm
bit2 = AppTerm bit2_tm

-- |View of numerals in Norrish format: using bits 1 and 2 only.
data Norrish =
    NZero
  | NBit1 Norrish
  | NBit2 Norrish

-- |Embed Norrish numerals in terms.
n2t :: Norrish -> Term
n2t NZero = zero
n2t (NBit1 n) = bit1 (n2t n)
n2t (NBit2 n) = bit2 (n2t n)

-- |View terms as Norrish numerals.
t2n :: Term -> Maybe Norrish
t2n tm = if tm == zero then return NZero else
         case tm of
           AppTerm b1 t | b1 == bit1_tm -> t2n t >>= return . NBit1
           AppTerm b2 t | b2 == bit2_tm -> t2n t >>= return . NBit2
           _ -> mzero

-- |View of numerals in binary: using bits 0 and 1 only.
data Binary =
    BZero
  | BBit0 Binary
  | BBit1 Binary

-- |Embed binary numerals in terms.
b2t :: Binary -> Term
b2t BZero = zero
b2t (BBit0 b) = bit0 (b2t b)
b2t (BBit1 b) = bit1 (b2t b)

-- |View terms as binary numerals.
t2b :: Term -> Maybe Binary
t2b tm = if tm == zero then return BZero else
         case tm of
           AppTerm b0 t | b0 == bit0_tm -> t2b t >>= return . BBit0
           AppTerm b1 t | b1 == bit1_tm -> t2b t >>= return . BBit1
           _ -> mzero
