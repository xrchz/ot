module OpenTheory.Object (Object(..)) where
import OpenTheory.Name
import OpenTheory.Type
import OpenTheory.Term
import OpenTheory.Proof

data Object =
    OTerm Term
  | OType Type
  | OPair (Object, Object)
  | OList [Object]
  | OName Name
  | OConst Const
  | OVar Var
  | OTypeOp TypeOp
  | OThm Proof
  | ONum Int
  deriving (Eq, Ord)
