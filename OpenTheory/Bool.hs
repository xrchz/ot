module OpenTheory.Bool (nsBool,truth,forall,forall_def) where
import OpenTheory.Name
import OpenTheory.Type
import OpenTheory.Term
import OpenTheory.Equality
import OpenTheory.Proof

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
