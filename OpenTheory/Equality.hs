-- |
-- Module      : $Header$
-- Copyright   : 2012, Ramana Kumar
-- License     : GPL
-- 
-- Maintainer  : ramana@xrchz.net
-- Stability   : experimental
-- Portability : non-portable (uses OpenTheory.Name)
-- 
-- OpenTheory equality terms. Equality is the only constant required to define the proof system in "OpenTheory.Proof".
module OpenTheory.Equality (eq,rhs,destEq,destEqTy) where
import OpenTheory.Name (nsMin)
import OpenTheory.Type (Type(),(-->),bool,dom)
import OpenTheory.Term (Term(ConstTerm,AppTerm),Const(Const))

eq_c :: Const
eq_c = Const (nsMin "=")

eq_tm :: Type -> Term
eq_tm ty = ConstTerm eq_c (ty --> ty --> bool)

-- |Build an equality term.
eq :: Type -> Term -> Term -> Term
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
-- consider making views of Term using typeclasses, so eq (and/or a
-- type-inferencing one) becomes a constructor

-- |Get both sides and the type of an equality term.
destEqTy :: Term -> (Type,Term,Term)
destEqTy (AppTerm (AppTerm (ConstTerm c ty) l) r) | c == eq_c = (dom ty,l,r)
destEqTy _ = error "destEqTy"

-- |Get both sides of an equality term.
destEq :: Term -> (Term,Term)
destEq tm = (l,r) where (_,l,r) = destEqTy tm

-- |Get a component of an equality term.
rhs :: Term -> Term
rhs = snd . destEq
