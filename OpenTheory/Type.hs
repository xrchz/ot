module OpenTheory.Type (Type(..),TypeOp(TypeOp),typeOp,subst,alpha,alpha_nm,fun,(-->),bool,dom,rng) where
import Data.Map (Map,findWithDefault)
import OpenTheory.Name (Name(),nsMin)

newtype TypeOp = TypeOp Name
  deriving (Eq, Ord)

data Type =
    OpType TypeOp [Type]
  | VarType Name
  deriving (Eq, Ord)

instance Show TypeOp where
  showsPrec d (TypeOp n) = showsPrec d n

instance Show Type where
  showsPrec d (VarType n) = showsPrec d n
  showsPrec d (OpType op [x,y]) | op == fun =
    showParen (d > prec) $
      showsPrec (prec+1) x .
      showString "->" .
      showsPrec (prec+1) y
    where prec = 1
  showsPrec d (OpType op args) = showArgs args . showsPrec d op
    where showArgs [] = id
          showArgs (a:as) = showsPrec d a . showString " " . showArgs as

typeOp :: Name -> [Type] -> Type
typeOp op as = OpType (TypeOp op) as

subst :: Map Name Type -> Type -> Type
subst s v@(VarType k) = findWithDefault v k s
subst s (OpType op args) = OpType op (map (subst s) args)

alpha_nm :: Name
alpha_nm = nsMin "A"

alpha :: Type
alpha = VarType alpha_nm

fun :: TypeOp
fun = TypeOp $ nsMin "->"
infixr -->
(-->) :: Type -> Type -> Type
x --> y = OpType fun [x, y]

bool :: Type
bool = typeOp (nsMin "bool") []

dom_rng :: Type -> (Type,Type)
dom_rng (OpType op [d,r]) | op == fun = (d,r)
dom_rng _ = error "dom_rng"

dom, rng :: Type -> Type
dom = fst . dom_rng
rng = snd . dom_rng
