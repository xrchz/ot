module OpenTheory.Bool (nsBool,truth,forall,forall_def) where
import OpenTheory.Name (Name(Name),name)
import OpenTheory.Type ((-->),bool,alpha)
import OpenTheory.Term (Term(..),Var(Var),Const(Const))
import OpenTheory.Equality (eq)
import OpenTheory.Proof (axiom)

nsBool = name ["Data","Bool"]

truth = ConstTerm (Const (nsBool "T")) bool

forall_tm ty = ConstTerm (Const (nsBool "!")) ((ty --> bool) --> bool)
forall v@(Var (_,ty)) bod = AppTerm (forall_tm ty) (AbsTerm v bod)

forall_def = axiom
  (eq ((alpha --> bool) --> bool)
    (forall_tm alpha)
    (AbsTerm p
      (eq (alpha --> bool)
        (VarTerm p)
        (AbsTerm x truth))))
  where
    x = Var (Name ([],"x"),alpha)
    p = Var (Name ([],"P"),alpha --> bool)
