module OpenTheory.Natural (nsNum,num,eq) where
import OpenTheory.Name (Name(),name,namespace)
import OpenTheory.Type (Type(),typeOp)
import OpenTheory.Term (Term())
import qualified OpenTheory.Equality as Eq (eq)

nsNum :: String -> Name
nsNum = name (namespace ["Number","Natural"])

num :: Type
num = typeOp (nsNum "natural") []

eq :: Term -> Term -> Term
eq = Eq.eq num
