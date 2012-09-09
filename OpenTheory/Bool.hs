-- |Boolean terms.
module OpenTheory.Bool (nsBool,true,forall,forall_def) where
import OpenTheory.Name (Name(),name,namespace)
import OpenTheory.Type (Type(),(-->),bool,alpha)
import OpenTheory.Term (Term(..),Var(Var),var,Const(Const))
import OpenTheory.Equality (eq)
import OpenTheory.Proof (Proof(),axiom)

-- |Make a name in the namespace for Boolean data.
nsBool :: String -> Name
nsBool = name (namespace ["Data","Bool"])

-- |True term.
true :: Term
true = ConstTerm (Const (nsBool "T")) bool

-- |Universal quantifier term.
forall_tm :: Type -> Term
forall_tm ty = ConstTerm (Const (nsBool "!")) ((ty --> bool) --> bool)

-- |Make a universally quantified term.
forall :: Var -> Term -> Term
forall v@(Var (_,ty)) bod = AppTerm (forall_tm ty) (AbsTerm v bod)

-- |Definition of the universal quantifier.
forall_def :: Proof
forall_def = axiom
  (eq ((alpha --> bool) --> bool)
    (forall_tm alpha)
    (AbsTerm p
      (eq (alpha --> bool)
        (VarTerm p)
        (AbsTerm x true))))
  where
    x = var "x" $ alpha
    p = var "P" $ alpha --> bool
