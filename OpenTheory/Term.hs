-- |Terms.
module OpenTheory.Term
( Term(..)
, Var(Var)
, var
, Const(Const)
, typeOf
, subst, substType
, rator, rand
) where
import Data.Set (Set)
import qualified Data.Set as Set (singleton,empty,union,delete,member)
import Data.Map (Map,findWithDefault,delete,singleton,insert)
import OpenTheory.Name (Name(Name),Component(Component),nsMin)
import OpenTheory.Type (Type(OpType),(-->),fun)
import qualified OpenTheory.Type as Type (subst)
import Prelude hiding (lex)

newtype Var = Var (Name, Type)
  deriving (Eq, Ord)

-- |Convenience function for building variables.
var :: String -> Type -> Var
var s ty = Var(nsMin s,ty)

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
  showsPrec d (Var(n,ty)) = showParen (d > prec) $
    showsPrec (prec+1) n .
    showChar ':' .
    showsPrec (prec+1) ty
    where prec = 1

instance Show Const where
  showsPrec d (Const n) = showsPrec d n

instance Show Term where
  showsPrec d (AbsTerm v b) = showParen (d > prec) $
    showChar '\\' .
    showsPrec d v .
    showChar '.' .
    showsPrec (prec+1) b
    where prec = 1
  showsPrec d (AppTerm t1 t2) = showParen (d > prec) $
    showsPrec (prec+1) t1 .
    showChar ' ' .
    showsPrec (prec+1) t2
    where prec = 2
  showsPrec d (ConstTerm c _) = showsPrec d c
  showsPrec d (VarTerm v) = showsPrec d v

typeOf :: Term -> Type
typeOf (VarTerm (Var (_,ty))) = ty
typeOf (ConstTerm _ ty) = ty
typeOf tm@(AppTerm f _) = case typeOf f of
  OpType op [_, r] | op == fun -> r
  ty -> error ("bad type: "++show ty++"\nfor rator of: "++show tm)
typeOf (AbsTerm (Var (_,x)) t) = x --> (typeOf t)

-- |Get a component of an application.
rator, rand :: Term -> Term
rator (AppTerm f _) = f
rator tm = error ("rator " ++ show tm)
rand  (AppTerm _ x) = x
rand  tm = error ("rand "  ++ show tm)

freeVars :: Term -> Set Var
freeVars (VarTerm v) = Set.singleton v
freeVars (ConstTerm _ _) = Set.empty
freeVars (AppTerm t1 t2) = freeVars t1 `Set.union` freeVars t2
freeVars (AbsTerm v b) = Set.delete v $ freeVars b

vary :: Var -> Var
vary (Var (Name(ns,Component n),ty)) = Var (Name(ns,Component$' ':n),ty)

variant :: Set Var -> Var -> Var
variant avoid = f where
  f v | Set.member v avoid = f (vary v)
  f v = v

-- |Substitute for variables within a term.
subst :: Map Var Term -> Term -> Term
subst s v@(VarTerm k) = findWithDefault v k s
subst _ c@(ConstTerm _ _) = c
subst s (AppTerm t1 t2) = AppTerm (subst s t1) (subst s t2)
subst s (AbsTerm v b) = AbsTerm v' (subst s' b) where
  v' = variant avoid v
  avoid = freeVars $ subst (delete v s) b
  s' = if v == v'
       then delete v s
       else insert v (VarTerm v') s

varSubstType :: Map Name Type -> Var -> Var
varSubstType s (Var (n,ty)) = Var (n,Type.subst s ty)

-- |Substitute for type variables within a term.
substType :: Map Name Type -> Term -> Term
substType s (VarTerm v) = VarTerm (varSubstType s v)
substType s (ConstTerm n ty) = ConstTerm n (Type.subst s ty)
substType s (AppTerm t1 t2) = AppTerm (substType s t1) (substType s t2)
substType s (AbsTerm v b) = AbsTerm (varSubstType s v) (substType s b)
