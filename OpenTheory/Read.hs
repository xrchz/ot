{-# LANGUAGE DeriveDataTypeable #-}
module OpenTheory.Read (RM,ReadState(..),readArticle,defaultHandler,thmsOnEOF,readTerm,putStack) where
import Data.Map (Map)
import qualified Data.Map as Map (lookup,insert,delete,fromList)
import qualified Data.List as List (map,foldl')
import Data.Maybe (fromJust)
import Data.Char (isDigit)
import Control.Monad.Trans.State (liftCatch)
import Data.Typeable (Typeable)
import Data.Dynamic (Dynamic)
import Control.Exception (Exception,try,throwIO,throw,catch)
import Control.Monad.State (StateT,get,put,liftIO)
import System.IO (Handle,hGetLine)
import OpenTheory.Name (Name(Name))
import OpenTheory.Type (Type(..),TypeOp(TypeOp))
import OpenTheory.Term (Term(..),Var(Var),Const(Const),rand)
import OpenTheory.Proof (Proof(Assume,AbsThm,EqMp,Refl,Subst,AppThm,DeductAntisym,BetaConv))
import OpenTheory.Object (Object(..))
import OpenTheory.Rule (proveHyp)
import Prelude hiding (log,map,getLine,catch)

data ReadState = ReadState {handle :: Handle, map :: Map Int Object, stack :: [Object], thms :: [Proof]}

type RM = StateT ReadState IO

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
getLine = get >>= (liftIO . try . hGetLine . handle)

-- in the absence of Data.DList...
type DList a = [a]
empty :: DList a
empty = []
toList :: DList a -> [a]
toList ls = ls
snoc :: DList a -> a -> DList a
snoc ls x = ls ++ [x]

readName :: String -> Name
readName s = r s empty empty where
  r [] ns n = Name (toList ns, toList n)
  r ('\\':c:cs) ns n = r cs ns (snoc n c)
  r ('.':cs) ns n = r cs (snoc ns (toList n)) empty
  r (c:cs) ns n = r cs ns (snoc n c)

data TermEx = TermEx Term
  deriving (Show, Typeable)
unEx :: TermEx -> Term
unEx (TermEx t) = t
instance Exception TermEx

defaultHandler :: Dynamic -> a
defaultHandler = throw

readTerm :: RM Term
readTerm = readArticle throwAxiom (return . rand . unEx) undefined where
  throwAxiom _ c _ = liftIO $ throwIO (TermEx c)

thmsOnEOF :: RM [Proof]
thmsOnEOF = get >>= return . thms

readArticle :: Exception e => ([Term] -> Term -> [Object] -> RM ()) -> (e -> RM a) -> RM a -> RM a
readArticle axiom handleError handleEOF = loop where
  loop = do
    result <- getLine
    case result of
      Left _ -> handleEOF
      Right line -> do
        liftCatch catch (rm >> loop) handleError
        where
        rm = case line of
          '"':s -> do
            st <- getStack
            putStack $ OName (readName (init s)) : st
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
