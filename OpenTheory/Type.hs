module OpenTheory.Type (Type(..),TypeOp(TypeOp),typeOp,subst,alpha,alpha_nm,(-->),bool,dom,rng) where
import Data.List (intercalate)
import Data.Map (Map,findWithDefault)
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

typeOp :: Name -> [Type] -> Type
typeOp op as = OpType (TypeOp op) as

subst :: Map Name Type -> Type -> Type
subst s v@(VarType k) = findWithDefault v k s
subst s (OpType op args) = OpType op (map (subst s) args)

alpha_nm :: Name
alpha_nm = Name ([],"A")

alpha :: Type
alpha = VarType alpha_nm

fn :: Name
fn = nsMin "->"
infixr -->
(-->) :: Type -> Type -> Type
x --> y = typeOp fn [x, y]

bool :: Type
bool = typeOp (nsMin "bool") []

dom_rng :: Type -> (Type,Type)
dom_rng (OpType (TypeOp op) [d,r]) | op == fn = (d,r)
dom_rng _ = error "dom_rng"

dom :: Type -> Type
dom = fst . dom_rng

rng :: Type -> Type
rng = snd . dom_rng
