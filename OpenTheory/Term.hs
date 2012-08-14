module OpenTheory.Term (Term(..),Var(Var),Const(Const),typeOf,rator,rand,subst,substType) where
import Data.Map (findWithDefault,delete)
import OpenTheory.Name (Name(Name))
import OpenTheory.Type (Type(OpType),(-->))
import qualified OpenTheory.Type as Type (subst)

newtype Var = Var (Name, Type)
  deriving (Eq, Ord)

newtype Const = Const Name
  deriving (Eq, Ord)

data Term =
    AbsTerm Var Term
  | AppTerm Term Term
  | ConstTerm Const Type
  | VarTerm Var
  deriving (Eq, Ord)

instance Show Var where
  show (Var(n,ty)) = "("++(show n)++":"++(show ty)++")"

instance Show Const where
  show (Const n) = show n

instance Show Term where
  show (AbsTerm v b) = "(\\"++(show v)++". "++(show b)++")"
  show (AppTerm (AppTerm (ConstTerm (Const (Name([],"="))) _) l) r) = "("++(show l)++" = "++(show r)++")"
  show (AppTerm t1 t2) = "("++(show t1)++" "++(show t2)++")"
  show (ConstTerm c _) = show c
  show (VarTerm v) = show v

typeOf (VarTerm (Var (_,ty))) = ty
typeOf (ConstTerm _ ty) = ty
typeOf tm@(AppTerm f _) = case typeOf f of
  OpType _ [_, r] -> r
  ty -> error ("bad type: "++show ty++"\nfor rator of: "++show tm)
typeOf (AbsTerm (Var (_,x)) t) = x --> (typeOf t)

rator (AppTerm f _) = f
rator tm = error ("rator " ++ show tm)

rand (AppTerm _ x) = x
rand tm = error ("rand " ++ show tm)

subst s v@(VarTerm k) = findWithDefault v k s
subst _ c@(ConstTerm _ _) = c
subst s (AppTerm t1 t2) = AppTerm (subst s t1) (subst s t2)
subst s (AbsTerm v b) = AbsTerm v (subst (delete v s) b)

varSubstType s (Var (n,ty)) = Var (n,Type.subst s ty)

substType s (VarTerm v) = VarTerm (varSubstType s v)
substType s (ConstTerm n ty) = ConstTerm n (Type.subst s ty)
substType s (AppTerm t1 t2) = AppTerm (substType s t1) (substType s t2)
substType s (AbsTerm v b) = AbsTerm (varSubstType s v) (substType s b)
