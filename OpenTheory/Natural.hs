module OpenTheory.Natural (nsNum,num,eq) where
import OpenTheory.Name (Name(),Component,name)
import OpenTheory.Type (Type(),typeOp)
import OpenTheory.Term (Term())
import qualified OpenTheory.Equality as Eq (eq)

nsNum :: Component -> Name
nsNum = name ["Number","Natural"]

num :: Type
num = typeOp (nsNum "natural") []

eq :: Term -> Term -> Term
eq = Eq.eq num
