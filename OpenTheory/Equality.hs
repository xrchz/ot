module OpenTheory.Equality (eq,rhs) where
import OpenTheory.Name
import OpenTheory.Type
import OpenTheory.Term
eq_tm ty = ConstTerm (Const (nsMin "=")) (ty --> ty --> bool)
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
-- consider making views of Term using typeclasses, so eq (and/or a
-- type-inferencing one) becomes a constructor

rhs = rand
