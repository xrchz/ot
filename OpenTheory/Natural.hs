module OpenTheory.Natural (nsNum,num,eq) where
import OpenTheory.Name
import OpenTheory.Type
import qualified OpenTheory.Equality as Eq
nsNum = name ["Number","Natural"]
num = typeOp (nsNum "natural") []
eq = Eq.eq num
