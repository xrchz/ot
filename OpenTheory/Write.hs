module OpenTheory.Write (WM,WriteState(..),logRawLn,logThm) where
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set (toAscList)
import qualified Data.Map as Map (toAscList,lookup,size,insert)
import Control.Monad.State (StateT,get,put,liftIO)
import System.IO (Handle,hPutStr,hPutStrLn)
import qualified Data.List as List (map)
import Prelude hiding (log,map)
import OpenTheory.Name (Name(Name))
import OpenTheory.Type (Type(..),TypeOp(TypeOp))
import OpenTheory.Term (Term(..),Var(Var),Const(Const))
import OpenTheory.Proof (Proof(..),hyp,concl)
import OpenTheory.Object (Object(..))

-- should use the reader monad for immutable state
data WriteState = WriteState {handle :: Handle, map :: Map Object Int}

type WM a = StateT WriteState IO a

getField :: (WriteState -> a) -> WM a
getField f = get >>= return . f

putMap :: Map Object Int -> WM ()
putMap m = do
  s <- get
  put (s {map = m})

class Loggable a where
  key :: a -> Object
  log :: a -> WM ()

logRaw, logRawLn :: String -> WM ()
logRaw s   = getField handle >>= liftIO . flip hPutStr s
logRawLn s = getField handle >>= liftIO . flip hPutStrLn s

logCommand :: String -> WM ()
logCommand = logRawLn

logNum :: Int -> WM ()
logNum = logCommand . show

hc :: Loggable a => (a -> WM ()) -> a -> WM ()
hc logA a = do
  m0 <- getField map
  case Map.lookup (key a) m0 of
    Just k -> do
      logNum k
      logCommand "ref"
    Nothing -> do
      logA a
      m <- getField map
      let k = Map.size m
      logNum k
      logCommand "def"
      putMap (Map.insert (key a) k m)

instance Loggable a => Loggable [a] where
  key = OList . (List.map key)
  log = hc l where
    l [] = logCommand "nil"
    l (x:xs) = do
      log x
      log xs
      logCommand "cons"

instance Loggable a => Loggable (Set a) where
  key = key . Set.toAscList
  log = log . Set.toAscList

instance (Loggable a, Loggable b) => Loggable (a,b) where
  key (a,b) = OPair (key a, key b)
  log = hc l where
    l (a,b) = do
      log a
      log b
      logCommand "nil"
      logCommand "cons"
      logCommand "cons"

instance (Loggable k, Loggable v) => Loggable (Map k v) where
  key = key . Map.toAscList
  log = log . Map.toAscList

instance Loggable Name where
  key = OName
  log = hc l where
    l (Name (ns,n)) = do
      logRaw $ "\""++show ns++show n
      logRawLn "\""

instance Loggable TypeOp where
  key = OTypeOp
  log = hc l where
    l (TypeOp t) = do
      log t
      logCommand "typeOp"

instance Loggable Type where
  key = OType
  log = hc l where
    l (OpType op args) = do
      log op
      log args
      logCommand "opType"
    l (VarType n) = do
      log n
      logCommand "varType"

instance Loggable Var where
  key = OVar
  log = hc l where
    l (Var (n,ty)) = do
      log n
      log ty
      logCommand "var"

instance Loggable Const where
  key = OConst
  log = hc l where
    l (Const c) = do
      log c
      logCommand "const"

instance Loggable Term where
  key = OTerm
  log = hc l where
    l (AbsTerm v t) = do
      log v
      log t
      logCommand "absTerm"
    l (AppTerm f x) = do
      log f
      log x
      logCommand "appTerm"
    l (ConstTerm c ty) = do
      log c
      log ty
      logCommand "constTerm"
    l (VarTerm v) = do
      log v
      logCommand "varTerm"

instance Loggable Proof where
  key = OThm
  log = hc l where
    l (Assume tm) = do
      log tm
      logCommand "assume"
    l (Refl tm) = do
      log tm
      logCommand "refl"
    l (Axiom hs tm) = do
      log hs
      log tm
      logCommand "axiom"
    l (EqMp th1 th2) = do
      log th1
      log th2
      logCommand "eqMp"
    l (AppThm th1 th2) = do
      log th1
      log th2
      logCommand "appThm"
    l (AbsThm v th) = do
      log v
      log th
      logCommand "absThm"
    l (BetaConv tm) = do
      log tm
      logCommand "betaConv"
    l (Subst sigma th) = do
      log sigma
      log th
      logCommand "subst"
    l (DeductAntisym th1 th2) = do
      log th1
      log th2
      logCommand "deductAntisym"

logThm :: Proof -> WM ()
logThm th = do
  log th
  log (hyp th)
  log (concl th)
  logCommand "thm"
