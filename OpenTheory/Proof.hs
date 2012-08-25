-- |Theorems, represented by proof trees.
module OpenTheory.Proof
( Proof(..)
, concl
, hyp
, axiom
) where
import Data.Set (Set)
import qualified Data.Set as Set (empty,union,delete,singleton,map)
import Data.Map (Map,singleton)
import OpenTheory.Name (Name())
import OpenTheory.Type (Type(),(-->),bool,rng)
import OpenTheory.Term (Term(AppTerm,AbsTerm),Var(Var),typeOf,substType)
import qualified OpenTheory.Term as Term (subst)
import OpenTheory.Equality (eq,rhs,destEq,destEqTy)

-- | There is a constructor for each primitive rule of inference in the OpenTheory kernel. (Currently some are missing.)
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

substBoth :: (Map Name Type, Map Var Term) -> Term -> Term
substBoth (sty,stm) = Term.subst stm . substType sty

-- | Conclusion of the proved theorem.
concl :: Proof -> Term
concl (Assume t) = t
concl (Refl t) = eq (typeOf t) t t
concl (AppThm th1 th2) = eq ty (AppTerm f1 x1) (AppTerm f2 x2)
  where (fn,f1,f2) = destEqTy (concl th1)
        (x1,x2) = destEq (concl th2)
        ty = rng fn
concl (AbsThm v th) = eq ty (AbsTerm v t1) (AbsTerm v t2)
  where (tt,t1,t2) = destEqTy (concl th)
        (Var (_,tv)) = v
        ty = tv --> tt
concl (EqMp th1 _) = rhs (concl th1)
concl (Axiom _ c) = c
concl (BetaConv tm) = case tm of
  AppTerm (AbsTerm v b) t -> eq (typeOf tm) tm (Term.subst (singleton v t) b)
  _ -> error ("concl BetaConv "++show tm)
concl (Subst s th) = substBoth s (concl th)
concl (DeductAntisym th1 th2) = eq bool (concl th1) (concl th2)

-- | Hypotheses of the proved theorem.
hyp :: Proof -> Set Term
hyp (Assume t) = Set.singleton t
hyp (Refl _) = Set.empty
hyp (AppThm th1 th2) = Set.union (hyp th1) (hyp th2)
hyp (AbsThm _ th) = hyp th
hyp (EqMp th1 th2) = Set.union (hyp th1) (hyp th2)
hyp (Axiom h _) = h
hyp (BetaConv _) = Set.empty
hyp (Subst s th) = Set.map (substBoth s) (hyp th)
hyp (DeductAntisym th1 th2) =
  Set.union
    (Set.delete (concl th2) (hyp th1))
    (Set.delete (concl th1) (hyp th2))

instance Ord Proof where
  compare th1 th2 =
    case compare (concl th1) (concl th2) of
      EQ -> compare (hyp th1) (hyp th2)
      x -> x

instance Eq Proof where
  th1 == th2 = compare th1 th2 == EQ

instance Show Proof where
  show th = show (hyp th) ++ " |- " ++ show (concl th)

-- | Create an axiom (without hypotheses).
axiom :: Term -> Proof
axiom = Axiom Set.empty
