module OpenTheory.Natural (nsNum,num,eq) where
import OpenTheory.Name (name)
import OpenTheory.Type (typeOp)
import qualified OpenTheory.Equality as Eq (eq)

nsNum = name ["Number","Natural"]
num = typeOp (nsNum "natural") []
eq = Eq.eq num
