import Data.Set (Set)
import Data.Map (Map)
import qualified Data.List as List
import qualified Data.Map as Map (empty,insert,lookup,size)
import Control.Monad (liftM)
import Control.Monad.State (StateT,get,put,liftIO,evalStateT,evalState)
import System.IO (Handle,withFile,IOMode(WriteMode),hPutStr,hPutStrLn)
import Prelude hiding (log,map)

data Norrish =
    NZero
  | NBit1 Norrish
  | NBit2 Norrish

data Binary =
    BZero
  | BBit0 Binary
  | BBit1 Binary

-- n2b n[Nor] = |- n[Nor] = n[Bin]
n2b NZero = Refl zero
n2b (NBit1 n) = AppThm (Refl bit1_tm) (n2b n)
n2b (NBit2 n) = trans (subs 2 (n2b n) (spec (n2t n) th1)) (binc (BBit1 nb))
  where nb = t2b (rhs (concl (n2b n)))

-- binc n[Bin] = |- suc n[Bin] = (n+1)[Bin]
binc BZero = th2
binc (BBit0 n) = spec (b2t n) th3
binc (BBit1 n) = subs 1 (binc n) (spec (b2t n) th4)

th1 = Axiom (forall vn (eqn (bit2 n) (suc (bit1 n))))
th2 = Axiom (eqn (suc zero) (bit1 zero))
th3 = Axiom (forall vn (eqn (suc (bit0 n)) (bit1 n)))
th4 = Axiom (forall vn (eqn (suc (bit1 n)) (bit0 (suc n))))

-- subs n (x = y) (|- l = r[x]) = |- l = r[y]
-- assumes x is the nth operand of r
subs n eq th = trans th (build n (rhs (concl th))) where
  build 0 _ = eq
  build n (AppTerm f x) = AppThm (Refl f) (build (n-1) x)

vn = Var (Name ([],"n"),num)
n  = VarTerm vn

bit_tm s = ConstTerm (Const (numns ("bit"++s))) (fn num num)
bit0_tm = bit_tm "0"
bit1_tm = bit_tm "1"
bit2_tm = bit_tm "2"
bit0 = AppTerm bit0_tm
bit1 = AppTerm bit1_tm
bit2 = AppTerm bit2_tm

zero = ConstTerm (Const (numns "zero")) num
suc  = AppTerm (ConstTerm (Const (numns "suc")) (fn num num))

-- Norrish -> Term
n2t NZero = zero
n2t (NBit1 n) = bit1 (n2t n)
n2t (NBit2 n) = bit2 (n2t n)

-- Term -> Binary
t2b tm = if tm == zero then BZero else
         if rator tm == bit0_tm then BBit0 (t2b (rand tm)) else
         if rator tm == bit1_tm then BBit1 (t2b (rand tm)) else error "t2b"
-- Binary -> Term
b2t BZero = zero
b2t (BBit0 b) = bit0 (b2t b)
b2t (BBit1 b) = bit1 (b2t b)

mkns ns s = Name (ns, s)
minns  = mkns []
numns  = mkns ["Number","Natural"]
boolns = mkns ["Data","Bool"]

mkty op as = OpType (TypeOp op) as
fn x y = mkty (minns "->")      [x, y]
bool   = mkty (minns "bool")    []
num    = mkty (numns "natural") []

eq_tm ty = ConstTerm (Const (minns "=")) (fn ty (fn ty bool))
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
eqn = eq num

rator (AppTerm f _) = f
rand (AppTerm _ x) = x
rhs = rand

truth = ConstTerm (Const (boolns "T")) bool

forall_tm ty = ConstTerm (Const (boolns "!")) (fn (fn ty bool) bool)
forall v@(Var (_,ty)) bod = AppTerm (forall_tm ty) (AbsTerm v bod)

forall_def = Axiom
  (eq (fn (fn alpha bool) bool)
    (forall_tm alpha)
    (AbsTerm p
      (eq (fn alpha bool)
        (VarTerm p)
        (AbsTerm x truth))))
  where
    x = Var (Name ([],"x"),alpha)
    p = Var (Name ([],"P"),fn alpha bool)

alpha_nm = Name ([],"A")
alpha = VarType alpha_nm

type Component = String
type Namespace = [Component]
newtype Name = Name (Namespace, Component)
  deriving (Eq, Ord)

newtype TypeOp = TypeOp Name
  deriving (Eq, Ord)

newtype Var = Var (Name, Type)
  deriving (Eq, Ord)

data Term =
    AbsTerm Var Term
  | AppTerm Term Term
  | ConstTerm Const Type
  | VarTerm Var
  deriving (Eq, Ord)

data Proof =
    Refl Term
  | AppThm Proof Proof
  | EqMp Proof Proof
  | Axiom Term
  | BetaConv Term
  | InstA Type Proof

trans th1 th2 = EqMp (AppThm (Refl t) th2) th1
  where t = rator (concl th1)

sym th = EqMp lel_rel lel
  where
    lel_rel = AppThm le_re lel
    lel = Refl l
    le_re = AppThm (Refl e) ler
    AppTerm (AppTerm e l) r = concl th
    ler = th

spec tm th = EqMp (sym pv_T) (Axiom truth)
  where
    pv_T = trans pv_lxPxv (trans lxPxv_lxTv lxTv_T)
    pv_lxPxv = sym (BetaConv lxPxv) -- P[v] = (\x. P[x]) v
    lxTv_T = BetaConv lxTv -- (\x. T) v = T
    AppTerm (AppTerm _ lxPxv) lxTv = concl lxPxv_lxTv
    lxPxv_lxTv = AppThm lxPx_lxT (Refl v) -- (\x. P[x]) v = (\x. T) v
    lxPx_lxT = EqMp bc lPP_lxTlxPx    -- (\x. P[x]) = (\x. T)
    bc = BetaConv (concl lPP_lxTlxPx) -- (\P. P = (\x. T)) (\x. P[x]) = (\x. P[x]) = (\x. T)
    lPP_lxTlxPx = EqMp faxPx_ fa_lxPx -- (\P. P = (\x. T)) (\x. P[x])
    faxPx_ = (AppThm fa_lPP_lxT (Refl lxPx)) -- (!x. P[x]) = (\P. P = (\x. T)) (\x. P[x])
    lxPx = rand (concl th)            -- (\x. P[x])
    fa_lPP_lxT = InstA ty forall_def  -- (!) = (\P. P = (\x. T))
    fa_lxPx = th                      -- !x. P[x]
    ty = tyof v
    v = tm

concl (Refl t) = eq (tyof t) t t
concl (AppThm th1 th2) = eq ty (AppTerm f1 x1) (AppTerm f2 x2)
  where (AppTerm (AppTerm _ f1) f2) = concl th1
        (AppTerm (AppTerm _ x1) x2) = concl th2
        (OpType _ [_,ty]) = tyof f1
concl (EqMp th1 th2) = rhs (concl th1)
concl (Axiom t) = t
concl (BetaConv tm@(AppTerm (AbsTerm v b) t)) = eq (tyof tm) tm (subst v t b)
concl (InstA ty th) = tminstA ty (concl th)

subst v t tm@(VarTerm v') = if v == v' then t else tm
subst _ _ tm@(ConstTerm _ _) = tm
subst v t (AppTerm t1 t2) = AppTerm (subst v t t1) (subst v t t2)
subst v t tm@(AbsTerm v' b) = if v == v' then tm else AbsTerm v' (subst v t b)

tyinstA t v@(VarType _) = if v == alpha then t else v
tyinstA t (OpType op args) = (OpType op (List.map (tyinstA t) args))
tminstA t tm = f tm
  where
    f (VarTerm (Var (v,ty))) = VarTerm (Var (v, g ty))
    f (ConstTerm c ty) = ConstTerm c (g ty)
    f (AppTerm t1 t2) = AppTerm (f t1) (f t2)
    f (AbsTerm (Var (v,ty)) tm) = AbsTerm (Var (v, g ty)) (f tm)
    g = tyinstA t

tyof (VarTerm (Var (_,ty))) = ty
tyof (ConstTerm _ ty) = ty
tyof (AppTerm f _) = r
  where OpType _ [_, r] = tyof f
tyof (AbsTerm (Var (_,x)) t) = fn x (tyof t)

data Object =
    OTerm Term
  | OType Type
  | OPair (Object, Object)
  | OList [Object]
  | OName Name
  | OConst Const
  | OVar Var
  | OTypeOp TypeOp
  | OThm Term
  deriving (Eq, Ord)

data State = State {handle :: Handle, map :: Map Object Int}

type M a = StateT State IO a

getHandle = get >>= return . handle
getMap = get >>= return . map
putMap m = do
  s <- get
  put (s {map = m})

class Loggable a where
  key :: a -> Object
  log :: a -> M ()

logRaw s = getHandle >>= liftIO . flip hPutStr s
logRawLn s = getHandle >>= liftIO . flip hPutStrLn s

logCommand = logRawLn

logNum = logCommand . (show :: Int -> String)

logComponent lr = lc where
  lc [] = return ()
  lc (x:xs) = do
    if elem x ".\"\\" then lr "\\" else return ()
    lr [x]
    lc xs

logNamespace lr = ln where
  ln [] = return ()
  ln (c:ns) = do
    lc c
    lr "."
    ln ns
  lc = logComponent logRaw

instance Loggable Name where
  key = OName
  log (Name (ns,n)) = do
    logRaw "\""
    logNamespace logRaw ns
    logComponent logRaw n
    logRawLn "\""

hc :: Loggable a => (a -> M ()) -> a -> M ()
hc log a = do
  m <- getMap
  case Map.lookup (key a) m of
    Just k -> do
      logNum k
      logCommand "ref"
    Nothing -> do
      log a
      m <- getMap
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

instance (Loggable a, Loggable b) => Loggable (a,b) where
  key (a,b) = OPair (key a, key b)
  log = hc l where
    l (a,b) = do
      log a
      log b
      logCommand "nil"
      logCommand "cons"
      logCommand "cons"

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
  key = OThm . concl
  log = hc l where
    l (Refl tm) = do
      log tm
      logCommand "refl"
    l (Axiom tm) = do
      log ([]::[Term])
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
    l (BetaConv tm) = do
      log tm
      logCommand "betaConv"
    l (InstA ty th) = do
      log ([(alpha_nm,ty)],[]::[(Var,Term)])
      log th
      logCommand "subst"

logThm th = do
  log th
  log ([]::[Term])
  log (concl th)
  logCommand "thm"

instance Show Name where
  show (Name (ns,n)) = evalState c "" where
    c = (logComponent l n) >> get
    l s2 = get >>= (\s1 -> put (s1 ++ s2))

instance Show TypeOp where
  show (TypeOp n) = show n
data Type =
    OpType TypeOp [Type]
  | VarType Name
  deriving (Eq, Ord)
instance Show Type where
  show (VarType n) = show n
  show (OpType (TypeOp (Name ([],"->"))) [x,y]) = "("++(show x)++"->"++(show y)++")"
  show (OpType op args) = (List.intercalate " " (List.map show args))++(show op)

instance Show Var where
  show (Var(n,ty)) = "("++(show n)++":"++(show ty)++")"
newtype Const = Const Name
  deriving (Eq, Ord)
instance Show Const where
  show (Const n) = show n

instance Show Term where
  show (AbsTerm v b) = "(\\"++(show v)++". "++(show b)++")"
  show (AppTerm (AppTerm (ConstTerm (Const (Name([],"="))) _) l) r) = "("++(show l)++" = "++(show r)++")"
  show (AppTerm t1 t2) = "("++(show t1)++" "++(show t2)++")"
  show (ConstTerm c ty) = show c
  show (VarTerm v) = show v

run h n = withFile h WriteMode f where
  f h = evalStateT (logThm (n2b n)) (init h)
  init h = State {handle=h, map=Map.empty}
