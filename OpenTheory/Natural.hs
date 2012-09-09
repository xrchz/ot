-- |Natural number terms.
module OpenTheory.Natural (nsNum,num,eq) where
import OpenTheory.Name (Name(),name,namespace)
import OpenTheory.Type (Type(),typeOp)
import OpenTheory.Term (Term())
import qualified OpenTheory.Equality as Eq (eq)

-- |Make a name in the namespace for natural numbers.
nsNum :: String -> Name
nsNum = name (namespace ["Number","Natural"])

-- |Type of natural numbers.
num :: Type
num = typeOp (nsNum "natural") []

-- |Make an equality of natural numbers term.
eq :: Term -> Term -> Term
eq = Eq.eq num
