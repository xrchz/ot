module OpenTheory.Proof (Proof(..),concl,hyp,axiom) where
import Data.Set (Set)
import qualified Data.Set as Set (empty,union,delete,singleton)
import Data.Map (Map,singleton)
import OpenTheory.Name (Name())
import OpenTheory.Type (Type(OpType),(-->),bool)
import OpenTheory.Term (Term(AppTerm,AbsTerm),Var(Var),typeOf,substType)
import qualified OpenTheory.Term as Term (subst)
import OpenTheory.Equality (eq,rhs)

data Proof =
    AbsThm Var Proof
  | AppThm Proof Proof
  | Assume Term
  | Axiom (Set Term) Term
  | BetaConv Term
  | DeductAntisym Proof Proof
  | EqMp Proof Proof
  | Refl Term
  | Subst (Map Name Type, Map Var Term) Proof

concl :: Proof -> Term
concl (Assume t) = t
concl (Refl t) = eq (typeOf t) t t
concl (AppThm th1 th2) = eq ty (AppTerm f1 x1) (AppTerm f2 x2)
  where (AppTerm (AppTerm _ f1) f2) = concl th1
        (AppTerm (AppTerm _ x1) x2) = concl th2
        (OpType _ [_,ty]) = typeOf f1
concl (AbsThm v th) = eq ty (AbsTerm v t1) (AbsTerm v t2)
  where (AppTerm (AppTerm _ t1) t2) = concl th
        (Var (_,tyv)) = v
        ty = tyv --> (typeOf t1)
concl (EqMp th1 _) = rhs (concl th1)
concl (Axiom _ c) = c
concl (BetaConv tm) = case tm of
  AppTerm (AbsTerm v b) t -> eq (typeOf tm) tm (Term.subst (singleton v t) b)
  _ -> error ("concl BetaConv "++show tm)
concl (Subst (sty,stm) th) = Term.subst stm (substType sty (concl th))
concl (DeductAntisym th1 th2) = eq bool (concl th1) (concl th2)

hyp :: Proof -> Set Term
hyp (Assume t) = Set.singleton t
hyp (Refl _) = Set.empty
hyp (AppThm th1 th2) = Set.union (hyp th1) (hyp th2)
hyp (AbsThm _ th) = hyp th
hyp (EqMp th1 th2) = Set.union (hyp th1) (hyp th2)
hyp (Axiom h _) = h
hyp (BetaConv _) = Set.empty
hyp (Subst _ _) = Set.empty
hyp (DeductAntisym th1 th2) =
  Set.union
    (Set.delete (concl th2) (hyp th1))
    (Set.delete (concl th1) (hyp th2))

instance Eq Proof where
  th1 == th2 =
    hyp th1 == hyp th2 &&
    concl th1 == concl th2

instance Ord Proof where
  compare th1 th2 =
    case compare (hyp th1) (hyp th2) of
      EQ -> compare (concl th1) (concl th2)
      x -> x

instance Show Proof where
  show th = show (hyp th) ++ " |- " ++ show (concl th)

axiom :: Term -> Proof
axiom = Axiom Set.empty
