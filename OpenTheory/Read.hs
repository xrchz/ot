{-# LANGUAGE DeriveDataTypeable #-}
module OpenTheory.Read (ReadState(..),readArticle,defaultHandler,thmsOnEOF,readTerm,putStack) where
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
putStack x = do
  s <- get
  put $ (s {stack = x})
addThm th = do
  s <- get
  put $ (s {thms = th : (thms s)})

getLine :: RM (Either IOError String)
getLine = get >>= (liftIO . try . hGetLine . handle)

-- in the absence of Data.DList...
empty = []
toList ls = ls
snoc ls x = ls ++ [x]

readName s = r s empty empty where
  r [] ns n = Name (toList ns, toList n)
  r ('\\':c:cs) ns n = r cs ns (snoc n c)
  r ('.':cs) ns n = r cs (snoc ns (toList n)) empty
  r (c:cs) ns n = r cs ns (snoc n c)

data TermEx = TermEx Term
  deriving (Show, Typeable)
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
    l <- getLine
    case l of
      Left _ -> handleEOF
      Right l -> do
        liftCatch catch (rm >> loop) handleError
        where
        rm = case l of
          '"':s -> do
            stack <- getStack
            putStack $ OName (readName (init s)) : stack
          s@(c:_) | isDigit c || c == '-' -> do
            stack <- getStack
            putStack $ ONum (read s) : stack
          "absTerm" -> do
            OTerm b : OVar v : stack <- getStack
            putStack $ OTerm (AbsTerm v b) : stack
          "absThm" -> do
            OThm th : OVar v : stack <- getStack
            putStack $ OThm (AbsThm v th) : stack
          "appTerm" -> do
            OTerm x : OTerm f : stack <- getStack
            putStack $ OTerm (AppTerm f x) : stack
          "appThm" -> do
            OThm th2 : OThm th1 : stack <- getStack
            putStack $ OThm (AppThm th1 th2) : stack
          "assume" -> do
            OTerm t : stack <- getStack
            putStack $ OThm (Assume t) : stack
          "axiom" -> do
            OTerm c : OList h : stack <- getStack
            axiom (List.map (\(OTerm tm) -> tm) h) c stack
          "betaConv" -> do
            OTerm t : stack <- getStack
            putStack $ OThm (BetaConv t) : stack
          "cons" -> do
            OList t : h : stack <- getStack
            putStack $ OList (h : t) : stack
          "const" -> do
            OName n : stack <- getStack
            putStack $ OConst (Const n) : stack
          "constTerm" -> do
            OType ty : OConst c : stack <- getStack
            putStack $ OTerm (ConstTerm c ty) : stack
          "deductAntisym" -> do
            OThm th2 : OThm th1 : stack <- getStack
            putStack $ OThm (DeductAntisym th1 th2) : stack
          "def" -> do
            ONum k : x : stack <- getStack
            s <- get
            put $ (s {stack = x : stack, map = Map.insert k x (map s)})
          "eqMp" -> do
            OThm th2 : OThm th1 : stack <- getStack
            putStack $ OThm (EqMp th1 th2) : stack
          "nil" -> do
            stack <- getStack
            putStack $ OList [] : stack
          "opType" -> do
            OList ls : OTypeOp op : stack <- getStack
            putStack $ OType (OpType op (List.map (\(OType t) -> t) ls)) : stack
          "pop" -> do
            _ : stack <- getStack
            putStack stack
          "ref" -> do
            s <- get
            let ONum k : st = stack s
            put $ (s {stack = fromJust (Map.lookup k (map s)) : st})
          "refl" -> do
            OTerm t : stack <- getStack
            putStack $ OThm (Refl t) : stack
          "remove" -> do
            s <- get
            let ONum k : st = stack s
            put $ (s {stack = fromJust (Map.lookup k (map s)) : st,
                           map = Map.delete k (map s)})
          "subst" -> do
            OThm th : OList [OList os1, OList os2] : stack <- getStack
            let s1 = List.map (\(OList [OName n, OType ty]) -> (n,ty)) os1
            let s2 = List.map (\(OList [OVar  v, OTerm tm]) -> (v,tm)) os2
            putStack $ OThm (Subst (Map.fromList s1, Map.fromList s2) th) : stack
          "thm" -> do
            OTerm c : OList oh : OThm th : stack <- getStack
            putStack stack
            let h = List.map (\(OTerm t) -> t) oh
            addThm $ List.foldl' (flip (proveHyp . Assume)) (EqMp (Refl c) th) h
          "typeOp" -> do
            OName n : stack <- getStack
            putStack $ OTypeOp (TypeOp n) : stack
          "var" -> do
            OType ty : OName n : stack <- getStack
            putStack $ OVar (Var (n,ty)) : stack
          "varTerm" -> do
            OVar v : stack <- getStack
            putStack $ OTerm (VarTerm v) : stack
          "varType" -> do
            OName n : stack <- getStack
            putStack $ OType (VarType n) : stack
          s -> error ("unknown article command: " ++ s)
