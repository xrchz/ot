module OpenTheory.Object (Object(..)) where
import OpenTheory.Name (Name())
import OpenTheory.Type (Type(),TypeOp())
import OpenTheory.Term (Term(),Var(),Const())
import OpenTheory.Proof (Proof())

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
