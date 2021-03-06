-- |Article writer.
-- Writes articles in the format described at <http://www.gilith.com/research/opentheory/article.html>.
module OpenTheory.Write (Loggable,WM,WriteState,logRawLn,logThm,evalWM) where
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set (toAscList)
import qualified Data.Map as Map (toAscList,lookup,size,insert,empty)
import Control.Monad.State (StateT,get,put,liftIO,evalStateT)
import Control.Monad.Reader (ReaderT,lift,ask,runReaderT)
import System.IO (Handle,hPutStrLn)
import qualified Data.List as List (map)
import Prelude hiding (log,map)
import OpenTheory.Name (Name(Name))
import OpenTheory.Type (Type(..),TypeOp(TypeOp))
import OpenTheory.Term (Term(..),Var(Var),Const(Const))
import OpenTheory.Proof (Proof(..),hyp,concl)
import OpenTheory.Object (Object(..))

-- |Article-writing state: a map for tracking objects saved in the virtual machine's dictionary.
type WriteState = Map Object Int

-- |Monad for article writing.
-- Includes the article-writing state and the handle on the destination for article commands.
type WM = StateT WriteState (ReaderT Handle IO)

evalWMState :: WM a -> Handle -> WriteState -> IO a
evalWMState m h s = flip runReaderT h $ evalStateT m s

initialState :: WriteState
initialState = Map.empty

-- |Run an article-writing action on the supplied destination.
-- The article-writing state starts empty.
evalWM :: WM a -> Handle -> IO a
evalWM m h = evalWMState m h initialState

-- |An object is @Loggable@ if it can be represented as a virtual machine object and constructed using article commands.
class Loggable a where
  -- |Representation as an @Object@.
  key :: a -> Object
  -- |Generate commands for construction.
  log :: a -> WM ()

-- |Write a newline-terminated string.
logRawLn :: String -> WM ()
logRawLn s = lift ask >>= liftIO . flip hPutStrLn s

logCommand :: String -> WM ()
logCommand = logRawLn

logNum :: Int -> WM ()
logNum = logCommand . show

-- |Make a function for writing an commands to build an object also write commands to save the object (keeping track in the article-writing state), and refer to existing objects in the dictionary if possible rather than rebuilding them.
hc :: Loggable a => (a -> WM ()) -> a -> WM ()
hc logA a = do
  m0 <- get
  case Map.lookup (key a) m0 of
    Just k -> do
      logNum k
      logCommand "ref"
    Nothing -> do
      logA a
      m <- get
      let k = Map.size m
      logNum k
      logCommand "def"
      put (Map.insert (key a) k m)

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
    l (Name (ns,n)) =
      logRawLn $ showChar '\"' $
        shows ns $ shows n $
        showChar '\"' ""

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

-- |Write commands to build a theorem object from a @Proof@ and mark it as one of the article's exports.
logThm :: Proof -> WM ()
logThm th = do
  log th
  log (hyp th)
  log (concl th)
  logCommand "thm"
