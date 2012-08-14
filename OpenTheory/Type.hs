module OpenTheory.Type (Type(..),TypeOp(TypeOp),typeOp,subst,alpha,alpha_nm,(-->),bool) where
import Data.List (intercalate)
import Data.Map (findWithDefault)
import OpenTheory.Name (Name(Name),nsMin)

newtype TypeOp = TypeOp Name
  deriving (Eq, Ord)

data Type =
    OpType TypeOp [Type]
  | VarType Name
  deriving (Eq, Ord)

instance Show TypeOp where
  show (TypeOp n) = show n

instance Show Type where
  show (VarType n) = show n
  show (OpType (TypeOp (Name ([],"->"))) [x,y]) = "("++(show x)++"->"++(show y)++")"
  show (OpType op args) = (intercalate " " (map show args))++(show op)

typeOp op as = OpType (TypeOp op) as

subst s v@(VarType k) = findWithDefault v k s
subst s (OpType op args) = OpType op (map (subst s) args)

alpha_nm = Name ([],"A")
alpha = VarType alpha_nm

infixr -->
x --> y = typeOp (nsMin "->") [x, y]
bool = typeOp (nsMin "bool") []
