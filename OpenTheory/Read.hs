{-# LANGUAGE DeriveDataTypeable #-}
-- |Article reader.
module OpenTheory.Read (RM,ReadState(..),readArticle,defaultAxiom,defaultHandler,thmsOnEOF,readTerm,putStack,evalRM) where
import Data.Map (Map)
import qualified Data.Map as Map (lookup,insert,delete,fromList,empty)
import qualified Data.Set as Set (fromList)
import qualified Data.List as List (map,foldl')
import Data.Maybe (fromJust)
import Data.Char (isDigit)
import qualified Control.Monad.Trans.State as State (liftCatch)
import qualified Control.Monad.Trans.Reader as Reader (liftCatch)
import Data.Typeable (Typeable)
import Data.Dynamic (Dynamic)
import Control.Exception (Exception,try,throwIO,throw,catch)
import Control.Monad.State (StateT,get,put,liftIO,evalStateT)
import Control.Monad.Reader (ReaderT,lift,ask,runReaderT)
import System.IO (Handle,hGetLine)
import OpenTheory.Type (Type(..),TypeOp(TypeOp))
import OpenTheory.Term (Term(..),Var(Var),Const(Const),rand)
import OpenTheory.Proof (Proof(Axiom,Assume,AbsThm,EqMp,Refl,Subst,AppThm,DeductAntisym,BetaConv))
import OpenTheory.Object (Object(..))
import OpenTheory.Rule (proveHyp)
import Prelude hiding (log,map,getLine,catch)

data ReadState = ReadState {map :: Map Int Object, stack :: [Object], thms :: [Proof]}

type RM = StateT ReadState (ReaderT Handle IO)

catchRM :: Exception e => RM a -> (e -> RM a) -> RM a
catchRM = State.liftCatch $ Reader.liftCatch catch

evalRMState :: RM a -> Handle -> ReadState -> IO a
evalRMState m h s = flip runReaderT h $ evalStateT m s

initialState :: ReadState
initialState = ReadState {map = Map.empty, stack = [], thms = []}

evalRM :: RM a -> Handle -> IO a
evalRM m h = evalRMState m h initialState

getStack :: RM [Object]
getStack = get >>= return . stack

putStack :: [Object] -> RM ()
putStack x = do
  s <- get
  put $ (s {stack = x})

addThm :: Proof -> RM ()
addThm th = do
  s <- get
  put $ (s {thms = th : (thms s)})

getLine :: RM (Either IOError String)
getLine = lift ask >>= (liftIO . try . hGetLine)

data TermEx = TermEx Term
  deriving (Show, Typeable)
unEx :: TermEx -> Term
unEx (TermEx t) = t
instance Exception TermEx

defaultHandler :: Dynamic -> a
defaultHandler = throw

defaultAxiom :: [Term] -> Term -> [Object] -> RM ()
defaultAxiom h c s = putStack $ OThm (Axiom (Set.fromList h) c) : s

readTerm :: RM Term
readTerm = readArticle throwAxiom (return . rand . unEx) errorOnEOF where
  throwAxiom _ c _ = liftIO $ throwIO (TermEx c)

errorOnEOF :: RM a
errorOnEOF = error "unexpected EOF"

thmsOnEOF :: RM [Proof]
thmsOnEOF = get >>= return . thms

readArticle :: Exception e => ([Term] -> Term -> [Object] -> RM ()) -> (e -> RM a) -> RM a -> RM a
readArticle axiom handleError handleEOF = loop where
  loop = do
    result <- getLine
    case result of
      Left _ -> handleEOF
      Right line -> catchRM (rm >> loop) handleError where
        rm = case line of
          '"':s -> do
            st <- getStack
            putStack $ OName (read (init s)) : st
          s@(c:_) | isDigit c || c == '-' -> do
            st <- getStack
            putStack $ ONum (read s) : st
          "absTerm" -> do
            OTerm b : OVar v : st <- getStack
            putStack $ OTerm (AbsTerm v b) : st
          "absThm" -> do
            OThm th : OVar v : st <- getStack
            putStack $ OThm (AbsThm v th) : st
          "appTerm" -> do
            OTerm x : OTerm f : st <- getStack
            putStack $ OTerm (AppTerm f x) : st
          "appThm" -> do
            OThm th2 : OThm th1 : st <- getStack
            putStack $ OThm (AppThm th1 th2) : st
          "assume" -> do
            OTerm t : st <- getStack
            putStack $ OThm (Assume t) : st
          "axiom" -> do
            OTerm c : OList h : st <- getStack
            axiom (List.map (\(OTerm tm) -> tm) h) c st
          "betaConv" -> do
            OTerm t : st <- getStack
            putStack $ OThm (BetaConv t) : st
          "cons" -> do
            OList t : h : st <- getStack
            putStack $ OList (h : t) : st
          "const" -> do
            OName n : st <- getStack
            putStack $ OConst (Const n) : st
          "constTerm" -> do
            OType ty : OConst c : st <- getStack
            putStack $ OTerm (ConstTerm c ty) : st
          "deductAntisym" -> do
            OThm th2 : OThm th1 : st <- getStack
            putStack $ OThm (DeductAntisym th1 th2) : st
          "def" -> do
            ONum k : x : st <- getStack
            s <- get
            put $ (s {stack = x : st, map = Map.insert k x (map s)})
          "eqMp" -> do
            OThm th2 : OThm th1 : st <- getStack
            putStack $ OThm (EqMp th1 th2) : st
          "nil" -> do
            st <- getStack
            putStack $ OList [] : st
          "opType" -> do
            OList ls : OTypeOp op : st <- getStack
            putStack $ OType (OpType op (List.map (\(OType t) -> t) ls)) : st
          "pop" -> do
            _ : st <- getStack
            putStack st
          "ref" -> do
            s <- get
            let ONum k : st = stack s
            put $ (s {stack = fromJust (Map.lookup k (map s)) : st})
          "refl" -> do
            OTerm t : st <- getStack
            putStack $ OThm (Refl t) : st
          "remove" -> do
            s <- get
            let ONum k : st = stack s
            put $ (s {stack = fromJust (Map.lookup k (map s)) : st,
                           map = Map.delete k (map s)})
          "subst" -> do
            OThm th : OList [OList os1, OList os2] : st <- getStack
            let s1 = List.map (\(OList [OName n, OType ty]) -> (n,ty)) os1
            let s2 = List.map (\(OList [OVar  v, OTerm tm]) -> (v,tm)) os2
            putStack $ OThm (Subst (Map.fromList s1, Map.fromList s2) th) : st
          "thm" -> do
            OTerm c : OList oh : OThm th : st <- getStack
            putStack st
            let h = List.map (\(OTerm t) -> t) oh
            addThm $ List.foldl' (flip (proveHyp . Assume)) (EqMp (Refl c) th) h
          "typeOp" -> do
            OName n : st <- getStack
            putStack $ OTypeOp (TypeOp n) : st
          "var" -> do
            OType ty : OName n : st <- getStack
            putStack $ OVar (Var (n,ty)) : st
          "varTerm" -> do
            OVar v : st <- getStack
            putStack $ OTerm (VarTerm v) : st
          "varType" -> do
            OName n : st <- getStack
            putStack $ OType (VarType n) : st
          s -> error ("unknown article command: " ++ s)
