module OpenTheory.Equality (eq,rhs,destEq) where
import OpenTheory.Name (nsMin)
import OpenTheory.Type (Type(),(-->),bool,dom)
import OpenTheory.Term (Term(ConstTerm,AppTerm),Const(Const),rand)

eq_c :: Const
eq_c = Const (nsMin "=")

eq_tm :: Type -> Term
eq_tm ty = ConstTerm eq_c (ty --> ty --> bool)

eq :: Type -> Term -> Term -> Term
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
-- consider making views of Term using typeclasses, so eq (and/or a
-- type-inferencing one) becomes a constructor

destEqTy :: Term -> (Type,Term,Term)
destEqTy (AppTerm (AppTerm (ConstTerm c ty) l) r) | c == eq_c = (dom ty,l,r)
destEqTy _ = error "destEqTy"

destEq :: Term -> (Term,Term)
destEq tm = (l,r) where (_,l,r) = destEqTy tm

rhs :: Term -> Term
rhs = rand
