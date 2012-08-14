module OpenTheory.Equality (eq,rhs) where
import OpenTheory.Name (nsMin)
import OpenTheory.Type ((-->),bool)
import OpenTheory.Term (Term(ConstTerm,AppTerm),Const(Const),rand)

eq_tm ty = ConstTerm (Const (nsMin "=")) (ty --> ty --> bool)
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
-- consider making views of Term using typeclasses, so eq (and/or a
-- type-inferencing one) becomes a constructor

rhs = rand
