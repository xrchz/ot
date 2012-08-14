module OpenTheory.Term (Term(..),Var(Var),Const(Const),typeOf,rator,rand,subst,substType) where
import Data.Set (Set)
import qualified Data.Set as Set (singleton,empty,union,delete,unions,member)
import Data.Map (Map,findWithDefault,delete,singleton,elems,insert,filterWithKey)
import OpenTheory.Name (Name(Name),nsMin)
import OpenTheory.Type (Type(OpType),(-->))
import qualified OpenTheory.Type as Type (subst)
import Prelude hiding (lex)

newtype Var = Var (Name, Type)
  deriving (Eq, Ord)

newtype Const = Const Name
  deriving (Eq, Ord)

data Term =
    AbsTerm Var Term
  | AppTerm Term Term
  | ConstTerm Const Type
  | VarTerm Var

lex :: Ordering -> Ordering -> Ordering
lex EQ o2 = o2
lex o1 _  = o1

instance Ord Term where
  compare (AbsTerm v1 t1) (AbsTerm v2 t2) | v1 == v2 =
    compare t1 t2
  compare (AbsTerm v1@(Var(_,ty1)) t1) (AbsTerm v2@(Var(_,ty2)) t2) | ty1 == ty2 =
    subst (singleton v1 v3) t1 `compare`
    subst (singleton v2 v3) t2 where
      v3 = VarTerm $ variant avoid (Var (nsMin"",ty1))
      avoid = Set.delete v1 (freeVars t1) `Set.union`
              Set.delete v2 (freeVars t2)
  compare (AbsTerm v1 _) (AbsTerm v2 _) =
    compare v1 v2

  compare (AppTerm f1 x1) (AppTerm f2 x2) =
    lex (compare f1 f2) (compare x1 x2)

  compare (ConstTerm c1 t1) (ConstTerm c2 t2) =
    lex (compare c1 c2) (compare t1 t2)

  compare (VarTerm v1) (VarTerm v2) =
    compare v1 v2

  compare (AbsTerm _ _) _ = LT
  compare _ (AbsTerm _ _) = GT
  compare (AppTerm _ _) _ = LT
  compare _ (AppTerm _ _) = GT
  compare (ConstTerm _ _) _ = LT
  compare _ (ConstTerm _ _) = GT

instance Eq Term where
  t1 == t2 = compare t1 t2 == EQ

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

typeOf :: Term -> Type
typeOf (VarTerm (Var (_,ty))) = ty
typeOf (ConstTerm _ ty) = ty
typeOf tm@(AppTerm f _) = case typeOf f of
  OpType _ [_, r] -> r
  ty -> error ("bad type: "++show ty++"\nfor rator of: "++show tm)
typeOf (AbsTerm (Var (_,x)) t) = x --> (typeOf t)

rator :: Term -> Term
rator (AppTerm f _) = f
rator tm = error ("rator " ++ show tm)

rand :: Term -> Term
rand (AppTerm _ x) = x
rand tm = error ("rand " ++ show tm)

freeVars :: Term -> Set Var
freeVars (VarTerm v) = Set.singleton v
freeVars (ConstTerm _ _) = Set.empty
freeVars (AppTerm t1 t2) = Set.union (freeVars t1) (freeVars t2)
freeVars (AbsTerm v b) = Set.delete v $ freeVars b

vary :: Var -> Var
vary (Var (Name(ns,n),ty)) = Var (Name(ns,n++"'"),ty)

variant :: Set Var -> Var -> Var
variant avoid = f where
  f v | Set.member v avoid = f (vary v)
  f v = v

subst :: Map Var Term -> Term -> Term
subst s v@(VarTerm k) = findWithDefault v k s
subst _ c@(ConstTerm _ _) = c
subst s (AppTerm t1 t2) = AppTerm (subst s t1) (subst s t2)
subst s (AbsTerm v b) = AbsTerm v' (subst s' b) where
  v' = variant avoid v
  avoid = Set.unions $ map freeVars willSubst
  willSubst = elems $ filterWithKey (\k _ -> Set.member k fvs) s
  fvs = Set.delete v $ freeVars b
  s' = if v == v'
       then delete v s
       else insert v (VarTerm v') s

varSubstType :: Map Name Type -> Var -> Var
varSubstType s (Var (n,ty)) = Var (n,Type.subst s ty)

substType :: Map Name Type -> Term -> Term
substType s (VarTerm v) = VarTerm (varSubstType s v)
substType s (ConstTerm n ty) = ConstTerm n (Type.subst s ty)
substType s (AppTerm t1 t2) = AppTerm (substType s t1) (substType s t2)
substType s (AbsTerm v b) = AbsTerm (varSubstType s v) (substType s b)
