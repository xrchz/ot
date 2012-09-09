-- |Conversions: building theorems from terms.
module OpenTheory.Conv (Conv,depthConv) where
import Control.Monad (mzero,mplus)
import OpenTheory.Term (Term(AppTerm,AbsTerm))
import OpenTheory.Proof (Proof(Refl,AppThm,AbsThm))

-- |Conversions are often designed to fail (because they perform tests) hence the @Maybe@ return type.
type Conv = Term -> Maybe Proof

orElseConv :: Conv -> Conv -> Conv
orElseConv c1 c2 tm = c1 tm `mplus` c2 tm

tryConv :: Conv -> Conv
tryConv c = orElseConv c (return . Refl)

-- |Traverse a term top-down, applying a conversion at each subterm, without recursing on the result when it succeeds.
depthConv :: Conv -> Conv
depthConv c = c `orElseConv` subConv (depthConv c)

subConv :: Conv -> Conv
subConv c = tryConv (appConv c `orElseConv` absConv c)

appConv :: Conv -> Conv
appConv c (AppTerm t1 t2) = do
  th1 <- tryConv c t1
  th2 <- tryConv c t2
  return (AppThm th1 th2)
appConv _ _ = mzero

absConv :: Conv -> Conv
absConv c (AbsTerm v tm) = do
  th <- tryConv c tm
  return (AbsThm v th)
absConv _ _ = mzero
