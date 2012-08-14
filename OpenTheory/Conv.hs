module OpenTheory.Conv (depthConv) where
import Control.Monad.Error (throwError,catchError)
import OpenTheory.Term (Term(AppTerm,AbsTerm))
import OpenTheory.Proof (Proof(Refl,AppThm,AbsThm))

type Conv = Term -> Either String Proof

tryConv :: Conv -> Conv
tryConv c tm = catchError (c tm) (const (return (Refl tm)))

orElseConv :: Conv -> Conv -> Conv
orElseConv c1 c2 tm = catchError (c1 tm) (const (c2 tm))

depthConv :: Conv -> Conv
depthConv c = c `orElseConv` subConv (depthConv c)

subConv :: Conv -> Conv
subConv c = tryConv (appConv c `orElseConv` absConv c)

appConv :: Conv -> Conv
appConv c (AppTerm t1 t2) = do
  th1 <- tryConv c t1
  th2 <- tryConv c t2
  return (AppThm th1 th2)
appConv _ _ = throwError "appConv"

absConv :: Conv -> Conv
absConv c (AbsTerm v tm) = do
  th <- tryConv c tm
  return (AbsThm v th)
absConv _ _ = throwError "absConv"
