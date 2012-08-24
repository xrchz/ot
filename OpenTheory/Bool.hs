module OpenTheory.Bool (nsBool,truth,forall,forall_def) where
import OpenTheory.Name (Name(),name,namespace)
import OpenTheory.Type (Type(),(-->),bool,alpha)
import OpenTheory.Term (Term(..),Var(Var),var,Const(Const))
import OpenTheory.Equality (eq)
import OpenTheory.Proof (Proof(),axiom)

nsBool :: String -> Name
nsBool = name (namespace ["Data","Bool"])

truth :: Term
truth = ConstTerm (Const (nsBool "T")) bool

forall_tm :: Type -> Term
forall_tm ty = ConstTerm (Const (nsBool "!")) ((ty --> bool) --> bool)

forall :: Var -> Term -> Term
forall v@(Var (_,ty)) bod = AppTerm (forall_tm ty) (AbsTerm v bod)

forall_def :: Proof
forall_def = axiom
  (eq ((alpha --> bool) --> bool)
    (forall_tm alpha)
    (AbsTerm p
      (eq (alpha --> bool)
        (VarTerm p)
        (AbsTerm x truth))))
  where
    x = var "x" $ alpha
    p = var "P" $ alpha --> bool
